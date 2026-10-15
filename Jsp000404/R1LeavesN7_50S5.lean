import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_50S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h999 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1080 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1081 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1082 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1083 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1084 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h1864 | h1864
  · linarith only [h1083, h1084, h1864, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1866 | h1866
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1867 | h1867
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1868 | h1868
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1869 | h1869
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1870 | h1870
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1871 | h1871
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1872 | h1872
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1873 | h1873
                  · linarith only [h1080, h1084, h1873, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1875 | h1875
                    · linarith only [h1081, h1864, h1875, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1877 | h1877
                      · linarith only [h1080, h1081, h1084, h1864, h1866, h1870, h1872, h1877, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases h1bigk with h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c | h1879c
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h0, hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h655, hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h884, hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h999, hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          rcases p1879_3 (m.d 0 1) (by simp) with h1885 | h1885
                          · linarith only [h1885, hlam, p1879_0]
                          · rcases p1879_3 (m.d 1 2) (by simp) with h1887 | h1887
                            · rcases p1879_3 (m.d 1 3) (by simp) with h1888 | h1888
                              · linarith only [h1866, h1888, hlam]
                              · linarith only [h1888, h655, hlam]
                            · linarith only [h1887, hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h1084, h1869, h1871, h1877, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1879_1]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h1081, h1083, h1084, h1871, h1877, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1879_1, u2ehi3]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h999, hc01, hc12, hlam, hphi, p1879_1]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          rcases p1879_3 (m.d 0 1) (by simp) with h1896 | h1896
                          · linarith only [h1896, hlam, p1879_0]
                          · rcases p1879_3 (m.d 1 2) (by simp) with h1898 | h1898
                            · rcases p1879_3 (m.d 1 3) (by simp) with h1899 | h1899
                              · rcases p1879_3 (m.d 1 4) (by simp) with h1900 | h1900
                                · linarith only [h1869, h1900, hlam]
                                · linarith only [h1900, h884, hlam]
                              · linarith only [h1899, hlam, p1879_0]
                            · linarith only [h0, h1898, hlam]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h1866, hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h1081, h1083, h1084, h1871, h1877, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1879_1, u2ehi3]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h1081, h1083, h1084, h1866, h1871, h1877, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1879_1, u2ehi3]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          rcases p1879_3 (m.d 0 1) (by simp) with h1909 | h1909
                          · linarith only [h1909, hlam, p1879_0]
                          · rcases p1879_3 (m.d 1 2) (by simp) with h1911 | h1911
                            · rcases p1879_3 (m.d 1 3) (by simp) with h1912 | h1912
                              · rcases p1879_3 (m.d 1 4) (by simp) with h1913 | h1913
                                · rcases p1879_3 (m.d 1 5) (by simp) with h1914 | h1914
                                  · linarith only [h1871, h1914, hlam]
                                  · linarith only [h1914, h999, hlam]
                                · linarith only [h1913, hlam, p1879_0]
                              · linarith only [h1912, h655, hlam]
                            · linarith only [h0, h1911, hlam]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h1867, hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h1869, hlam, p1879_1]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h1081, h1083, h1084, h1871, h1877, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1879_1, u2ehi3]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          rcases p1879_3 (m.d 0 1) (by simp) with h1924 | h1924
                          · linarith only [h1924, hlam, p1879_0]
                          · rcases p1879_3 (m.d 1 2) (by simp) with h1926 | h1926
                            · rcases p1879_3 (m.d 1 3) (by simp) with h1927 | h1927
                              · rcases p1879_3 (m.d 1 4) (by simp) with h1928 | h1928
                                · rcases p1879_3 (m.d 1 5) (by simp) with h1929 | h1929
                                  · rcases h4bigk with h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [hlam, p1930_0]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h884, hlam, p1930_1]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1083, h1084, hc35, hlam, hphi, ht23, p1930_1, u2ehi3]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1083, h1084, h1877, hc34, hc45, hlam, hphi, p1930_1]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1864, hlam, p1930_0]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      rcases p1930_3 (m.d 0 4) (by simp) with h1936 | h1936
                                      · linarith only [h1936, h884, hlam]
                                      · rcases p1930_3 (m.d 1 4) (by simp) with h1938 | h1938
                                        · rcases p1930_3 (m.d 2 4) (by simp) with h1939 | h1939
                                          · linarith only [h1867, h1939, hlam]
                                          · rcases p1930_3 (m.d 3 4) (by simp) with h1941 | h1941
                                            · linarith only [h1869, h1941, hlam]
                                            · rcases p1930_3 (m.d 4 5) (by simp) with h1943 | h1943
                                              · linarith only [h1871, h1943, hlam]
                                              · linarith only [h1864, h1943, hlam]
                                        · linarith only [h1938, h884, hlam]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [hlam, p1930_0]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      rcases p1930_3 (m.d 0 4) (by simp) with h1948 | h1948
                                      · linarith only [h1948, h884, hlam]
                                      · linarith only [h1081, h1948, hlam]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1083, h1084, h1871, h1877, hlam, p1930_2]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1084, h1866, h1869, h1877, h655, hc01, hc12, hlam, hphi, p1930_1]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1081, hlam, p1930_0]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1867, hlam, p1930_0]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [hlam, p1930_0]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1080, h1084, h1872, h1877, hc34, hc45, hlam, hphi, p1930_1]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1875, hlam, p1930_0]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1083, hlam, p1930_0]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1869, hlam, p1930_0]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1872, hlam, p1930_0]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [hlam, p1930_0]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1877, hlam, p1930_0]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1081, hc45, hlam, hphi, ht23, ht34, p1930_1, u2ehi3]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1871, hlam, p1930_0]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [h1866, h1869, h1871, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1930_1, u2ehi3]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      rcases p1930_3 (m.d 0 4) (by simp) with h1966 | h1966
                                      · linarith only [h1864, h1966, hlam]
                                      · linarith only [h1083, h1966, hlam]
                                    · have p1930_0 := h1930c.1
                                      have p1930_1 := h1930c.2.1
                                      have p1930_2 := h1930c.2.2.1
                                      have p1930_3 := h1930c.2.2.2
                                      linarith only [hlam, p1930_0]
                                  · linarith only [h1929, hlam, p1879_0]
                                · linarith only [h1928, h884, hlam]
                              · linarith only [h1927, h655, hlam]
                            · linarith only [h0, h1926, hlam]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h1868, hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h1870, hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [h1871, hlam, p1879_0]
                        · have p1879_0 := h1879c.1
                          have p1879_1 := h1879c.2.1
                          have p1879_2 := h1879c.2.2.1
                          have p1879_3 := h1879c.2.2.2
                          linarith only [hlam, p1879_0]
                · linarith only [h1083, h1084, h1872, hc23, hc35, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1979 | h1979
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1980 | h1980
                  · linarith only [h0, h1080, h1084, h1980, h655, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1982 | h1982
                    · linarith only [h1871, h1982, h884, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1984 | h1984
                      · linarith only [h1080, h1084, h1866, h1870, h1871, h1979, h1984, h884, hc01, hc12, hlam, hphi]
                      · rcases h1bigk with h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [hlam, p1986_0]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h0, hlam, p1986_0]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h655, hlam, p1986_0]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h884, hlam, p1986_0]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h999, hlam, p1986_0]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          rcases p1986_3 (m.d 0 1) (by simp) with h1992 | h1992
                          · linarith only [h1992, hlam, p1986_0]
                          · rcases p1986_3 (m.d 1 2) (by simp) with h1994 | h1994
                            · rcases p1986_3 (m.d 1 3) (by simp) with h1995 | h1995
                              · linarith only [h1866, h1995, hlam]
                              · linarith only [h1995, h655, hlam]
                            · linarith only [h1994, hlam, p1986_0]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [hlam, p1986_0]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h1081, h1083, h1084, h1870, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1986_1, u2ehi3]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h884, hc01, hc12, hlam, hphi, p1986_1]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h999, hc01, hc12, hlam, hphi, p1986_1]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          rcases p1986_3 (m.d 0 1) (by simp) with h2003 | h2003
                          · linarith only [h2003, hlam, p1986_0]
                          · rcases p1986_3 (m.d 1 2) (by simp) with h2005 | h2005
                            · rcases p1986_3 (m.d 1 3) (by simp) with h2006 | h2006
                              · rcases p1986_3 (m.d 1 4) (by simp) with h2007 | h2007
                                · linarith only [h1869, h2007, hlam]
                                · linarith only [h2007, h884, hlam]
                              · linarith only [h2006, hlam, p1986_0]
                            · linarith only [h0, h2005, hlam]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h1866, hlam, p1986_0]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [hlam, p1986_0]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h884, hc01, hc13, hlam, hphi, p1986_1]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h1081, h1083, h1084, h1866, h1870, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1986_1, u2ehi3]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h1871, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1986_1]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h1867, hlam, p1986_0]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h1869, hlam, p1986_1]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [hlam, p1986_0]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h1871, hlam, p1986_1]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          rcases p1986_3 (m.d 0 1) (by simp) with h2021 | h2021
                          · linarith only [h2021, hlam, p1986_0]
                          · rcases p1986_3 (m.d 1 2) (by simp) with h2023 | h2023
                            · rcases p1986_3 (m.d 1 3) (by simp) with h2024 | h2024
                              · rcases p1986_3 (m.d 1 4) (by simp) with h2025 | h2025
                                · linarith only [h1871, h2025, hlam]
                                · linarith only [h2025, h884, hlam]
                              · linarith only [h2024, h655, hlam]
                            · linarith only [h0, h2023, hlam]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h1868, hlam, p1986_0]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h1870, hlam, p1986_0]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [h884, hc01, hc15, hlam, hphi, p1986_1]
                        · have p1986_0 := h1986c.1
                          have p1986_1 := h1986c.2.1
                          have p1986_2 := h1986c.2.2.1
                          have p1986_3 := h1986c.2.2.2
                          linarith only [hlam, p1986_0]
                · linarith only [h1083, h1084, h1866, h1870, h1979, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2035 | h2035
              · linarith only [h1081, h1864, h1869, h1870, h2035, hc35, hlam, hphi, ht23, u2ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2037 | h2037
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2038 | h2038
                  · linarith only [h1080, h1870, h2038, h655, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2040 | h2040
                    · linarith only [h1081, h2035, h2040, h884, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2042 | h2042
                      · linarith only [h1080, h1870, h2035, h2037, h2042, h655, h884, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases h1bigk with h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h0, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h655, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h884, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h999, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          rcases p2044_3 (m.d 0 1) (by simp) with h2050 | h2050
                          · linarith only [h2050, hlam, p2044_0]
                          · rcases p2044_3 (m.d 1 2) (by simp) with h2052 | h2052
                            · rcases p2044_3 (m.d 1 3) (by simp) with h2053 | h2053
                              · linarith only [h1866, h2053, hlam]
                              · linarith only [h2053, h655, hlam]
                            · linarith only [h2052, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h655, hc01, hc12, hlam, hphi, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h884, hc01, hc12, hlam, hphi, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h999, hc01, hc12, hlam, hphi, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1870, hc01, hc35, hlam, hphi, ht12, ht23, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1866, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1870, h2042, h884, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1870, hlam, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1869, h1870, h2042, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1867, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1869, hlam, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h2035, hlam, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          rcases p2044_3 (m.d 0 1) (by simp) with h2071 | h2071
                          · linarith only [h2071, hlam, p2044_0]
                          · rcases p2044_3 (m.d 1 2) (by simp) with h2073 | h2073
                            · rcases p2044_3 (m.d 1 3) (by simp) with h2074 | h2074
                              · linarith only [h1870, h2074, hlam]
                              · linarith only [h2074, h655, hlam]
                            · linarith only [h0, h2073, hlam]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1868, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h655, hc01, hc15, hlam, hphi, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1870, h2042, h884, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [hlam, p2044_0]
                · linarith only [h1083, h1084, h2035, h2037, h999, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h1083, h1869, h655, hlam]
        · linarith only [h0, h1080, h1868, hc25, hlam, hphi, u2ehi2]
      · linarith only [h0, h1081, h1867, hlam]
    · linarith only [h0, h1080, h1866, hlam]

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h999 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1080 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1081 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1082 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1083 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h1084 | h1084
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h655 h884 h999 h1080 h1081 h1082 h1083 h1084
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h655 h884 h999 h1080 h1081 h1082 h1083 h1084

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h999 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1080 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1081 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1082 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1083 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h2087 | h2087
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2088 | h2088
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2089 | h2089
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2090 | h2090
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2091 | h2091
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2092 | h2092
            · linarith only [h1083, h2087, h2092, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2094 | h2094
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2095 | h2095
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2096 | h2096
                  · linarith only [h1080, h1083, h2087, h2096, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2098 | h2098
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2099 | h2099
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2100 | h2100
                        · rcases h1bigk with h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h0, hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h655, hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h884, hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h999, hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            rcases p2101_3 (m.d 0 1) (by simp) with h2107 | h2107
                            · linarith only [h2107, hlam, p2101_0]
                            · rcases p2101_3 (m.d 1 2) (by simp) with h2109 | h2109
                              · rcases p2101_3 (m.d 1 3) (by simp) with h2110 | h2110
                                · linarith only [h2089, h2110, hlam]
                                · linarith only [h2110, h655, hlam]
                              · linarith only [h2109, hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h655, hc01, hc12, hlam, hphi, p2101_1]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h1080, h1083, h2098, h2100, h884, hc12, hlam, hphi, ht01, ht0b, ht5b, p2101_1, u5ehi4]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h999, hc01, hc12, hlam, hphi, p2101_1]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h2092, hc01, hc34, hlam, hphi, ht12, ht23, p2101_1]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h2089, hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h2092, hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h2092, h999, hc01, hc14, hlam, hphi, p2101_1]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            rcases p2101_3 (m.d 0 1) (by simp) with h2123 | h2123
                            · linarith only [h2123, hlam, p2101_0]
                            · rcases p2101_3 (m.d 1 2) (by simp) with h2125 | h2125
                              · rcases p2101_3 (m.d 1 3) (by simp) with h2126 | h2126
                                · linarith only [h2092, h2126, hlam]
                                · linarith only [h2126, h655, hlam]
                              · linarith only [h0, h2125, hlam]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h2090, hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h2092, h655, hc01, hc34, hlam, hphi, ht12, ht23, p2101_1]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h1082, h2092, h999, hc34, hlam, hphi, ht23, p2101_1, u2ehi4]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h2092, h2094, hc01, hc34, hlam, hphi, ht12, ht23, p2101_1]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h2091, hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h2094, hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [h2095, hlam, p2101_0]
                          · have p2101_0 := h2101c.1
                            have p2101_1 := h2101c.2.1
                            have p2101_2 := h2101c.2.2.1
                            have p2101_3 := h2101c.2.2.2
                            linarith only [hlam, p2101_0]
                        · linarith only [h2092, h2100, h655, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h2087, h2088, h2092, h2099, h655, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h2087, h2092, h2098, h655, hc34, hlam, hphi, ht23, u2ehi2]
                · linarith only [h2087, h2088, h2092, h2095, h655, h884, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h2087, h2094, h655, hlam]
          · linarith only [h0, h1080, h2091, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h1080, h2090, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h1080, h2089, hlam]
    · linarith only [h1083, h2087, h2088, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2148 | h2148
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2149 | h2149
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2150 | h2150
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2151 | h2151
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2152 | h2152
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2153 | h2153
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2154 | h2154
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2155 | h2155
                  · linarith only [h0, h1080, h1083, h2155, h655, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2157 | h2157
                    · linarith only [h1080, h2087, h2157, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2159 | h2159
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2160 | h2160
                        · rcases h1bigk with h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h0, hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h655, hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h884, hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h999, hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            rcases p2161_3 (m.d 0 1) (by simp) with h2167 | h2167
                            · linarith only [h2167, hlam, p2161_0]
                            · rcases p2161_3 (m.d 1 2) (by simp) with h2169 | h2169
                              · rcases p2161_3 (m.d 1 3) (by simp) with h2170 | h2170
                                · linarith only [h2149, h2170, hlam]
                                · linarith only [h2170, h655, hlam]
                              · linarith only [h2169, hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h1080, h2087, h2152, h2160, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2161_1, u2ehi2]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h1080, h2087, h2153, h2154, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2161_1, u2ehi2]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h1080, h2087, h2153, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2161_1, u2ehi2]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            rcases p2161_3 (m.d 0 1) (by simp) with h2178 | h2178
                            · linarith only [h2178, hlam, p2161_0]
                            · rcases p2161_3 (m.d 1 2) (by simp) with h2180 | h2180
                              · rcases p2161_3 (m.d 1 3) (by simp) with h2181 | h2181
                                · rcases p2161_3 (m.d 1 4) (by simp) with h2182 | h2182
                                  · linarith only [h2152, h2182, hlam]
                                  · linarith only [h2182, h884, hlam]
                                · linarith only [h2181, hlam, p2161_0]
                              · linarith only [h0, h2180, hlam]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h2149, hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h1080, h2087, h2153, h2154, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2161_1, u2ehi2]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h1080, h2087, h2149, h2153, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2161_1, u2ehi2]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            rcases p2161_3 (m.d 0 1) (by simp) with h2191 | h2191
                            · linarith only [h2191, hlam, p2161_0]
                            · rcases p2161_3 (m.d 1 2) (by simp) with h2193 | h2193
                              · rcases p2161_3 (m.d 1 3) (by simp) with h2194 | h2194
                                · rcases p2161_3 (m.d 1 4) (by simp) with h2195 | h2195
                                  · rcases p2161_3 (m.d 1 5) (by simp) with h2196 | h2196
                                    · linarith only [h2154, h2196, hlam]
                                    · linarith only [h2196, h999, hlam]
                                  · linarith only [h2195, hlam, p2161_0]
                                · linarith only [h2194, h655, hlam]
                              · linarith only [h0, h2193, hlam]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h2150, hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h2152, hlam, p2161_1]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h1080, h2087, h2153, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2161_1, u2ehi2]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            rcases p2161_3 (m.d 0 1) (by simp) with h2206 | h2206
                            · linarith only [h2206, hlam, p2161_0]
                            · rcases p2161_3 (m.d 1 2) (by simp) with h2208 | h2208
                              · rcases p2161_3 (m.d 1 3) (by simp) with h2209 | h2209
                                · rcases p2161_3 (m.d 1 4) (by simp) with h2210 | h2210
                                  · rcases p2161_3 (m.d 1 5) (by simp) with h2211 | h2211
                                    · rcases h4bigk with h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [hlam, p2212_0]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h884, hlam, p2212_1]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h2159, hc04, hlam, hphi, ht0b, ht5b, p2212_1, u5ehi4]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h1083, hlam, p2212_1]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h1083, h2149, h2152, hc12, hlam, hphi, ht01, ht0b, ht5b, p2212_1, u5ehi4]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h1081, h2149, h2152, h2159, hc12, hlam, hphi, ht01, ht0b, ht5b, p2212_1, u5ehi4]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [hlam, p2212_0]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h2149, h2152, h2159, hc12, hlam, hphi, ht01, ht0b, ht5b, p2212_1, u5ehi4]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h1080, h1083, h2149, h2152, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2212_1, u2ehi2]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        rcases p2212_3 (m.d 0 4) (by simp) with h2222 | h2222
                                        · linarith only [h2222, h884, hlam]
                                        · linarith only [h2148, h2222, hlam]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h1081, hlam, p2212_0]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h2150, hlam, p2212_0]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [hlam, p2212_0]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h2155, hlam, p2212_1]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h0, h1081, hc12, hlam, hphi, ht01, ht0b, ht5b, p2212_1, u5ehi4]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h1081, hc34, hlam, hphi, ht23, p2212_1, u2ehi3]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h2152, hlam, p2212_0]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h2149, h2152, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2212_1, u2ehi3]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [hlam, p2212_0]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h2149, h2152, hc12, hlam, hphi, ht01, ht0b, ht5b, p2212_1, u5ehi4]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h2148, hlam, p2212_0]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h2154, hlam, p2212_0]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h2159, hlam, p2212_0]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [h2160, hlam, p2212_0]
                                      · have p2212_0 := h2212c.1
                                        have p2212_1 := h2212c.2.1
                                        have p2212_2 := h2212c.2.2.1
                                        have p2212_3 := h2212c.2.2.2
                                        linarith only [hlam, p2212_0]
                                    · linarith only [h2211, hlam, p2161_0]
                                  · linarith only [h2210, h884, hlam]
                                · linarith only [h2209, h655, hlam]
                              · linarith only [h0, h2208, hlam]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h2151, hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h2153, hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [h2154, hlam, p2161_0]
                          · have p2161_0 := h2161c.1
                            have p2161_1 := h2161c.2.1
                            have p2161_2 := h2161c.2.2.1
                            have p2161_3 := h2161c.2.2.2
                            linarith only [hlam, p2161_0]
                        · linarith only [h1080, h1081, h1083, h2159, h2160, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h1083, h2148, h2149, h2152, h2159, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h1083, h2148, h2149, h2152, h2154, h884, hc01, hc12, hlam, hphi]
              · linarith only [h1083, h2148, h2152, h2153, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2252 | h2252
              · linarith only [h1080, h2087, h2152, h2252, hc34, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2254 | h2254
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2255 | h2255
                  · linarith only [h1080, h2152, h2255, h655, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2257 | h2257
                    · linarith only [h1080, h2087, h2257, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2259 | h2259
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2260 | h2260
                        · rcases h1bigk with h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h0, hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h655, hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h884, hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h999, hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            rcases p2261_3 (m.d 0 1) (by simp) with h2267 | h2267
                            · linarith only [h2267, hlam, p2261_0]
                            · rcases p2261_3 (m.d 1 2) (by simp) with h2269 | h2269
                              · rcases p2261_3 (m.d 1 3) (by simp) with h2270 | h2270
                                · linarith only [h2149, h2270, hlam]
                                · linarith only [h2270, h655, hlam]
                              · linarith only [h2269, hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h655, hc01, hc12, hlam, hphi, p2261_1]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h884, hc01, hc12, hlam, hphi, p2261_1]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h999, hc01, hc12, hlam, hphi, p2261_1]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h2252, h2260, hc01, hc34, hlam, hphi, ht12, ht23, p2261_1]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h2149, hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h2152, hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h2252, hlam, p2261_1]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            rcases p2261_3 (m.d 0 1) (by simp) with h2283 | h2283
                            · linarith only [h2283, hlam, p2261_0]
                            · rcases p2261_3 (m.d 1 2) (by simp) with h2285 | h2285
                              · rcases p2261_3 (m.d 1 3) (by simp) with h2286 | h2286
                                · linarith only [h2152, h2286, hlam]
                                · linarith only [h2286, h655, hlam]
                              · linarith only [h0, h2285, hlam]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h2150, hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h655, hc01, hc14, hlam, hphi, p2261_1]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h1080, h2087, h2152, h999, hc34, hlam, hphi, ht23, p2261_1, u2ehi2]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            rcases p2261_3 (m.d 0 1) (by simp) with h2294 | h2294
                            · linarith only [h2294, hlam, p2261_0]
                            · rcases p2261_3 (m.d 1 2) (by simp) with h2296 | h2296
                              · rcases p2261_3 (m.d 1 3) (by simp) with h2297 | h2297
                                · linarith only [h2252, h2297, hlam]
                                · linarith only [h2297, h655, hlam]
                              · linarith only [h0, h2296, hlam]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h2151, hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h655, hc01, hc15, hlam, hphi, p2261_1]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [h2254, hlam, p2261_0]
                          · have p2261_0 := h2261c.1
                            have p2261_1 := h2261c.2.1
                            have p2261_2 := h2261c.2.2.1
                            have p2261_3 := h2261c.2.2.2
                            linarith only [hlam, p2261_0]
                        · linarith only [h2152, h2259, h2260, h884, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h1083, h2148, h2259, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h2148, h2254, h884, hlam]
          · linarith only [h0, h1082, h2151, hlam]
        · linarith only [h0, h1082, h2150, hc24, hlam, hphi, u2ehi4]
      · linarith only [h0, h1081, h2149, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2311 | h2311
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2312 | h2312
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2313 | h2313
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2314 | h2314
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2315 | h2315
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2316 | h2316
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2317 | h2317
                  · linarith only [h1080, h1083, h2317, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2319 | h2319
                    · linarith only [h1080, h1083, h2148, h2314, h2316, h2319, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2321 | h2321
                      · linarith only [h1080, h1083, h2148, h2321, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2323 | h2323
                        · linarith only [h1080, h1083, h2148, h2323, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h1080, h1083, h2311, h2314, h2316, h2323, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h1080, h1083, h2314, h2316, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h1080, h1083, h2314, h2315, hc35, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2328 | h2328
              · linarith only [h1080, h2087, h2314, h2328, hc34, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2330 | h2330
                · linarith only [h1081, h2148, h2314, h2330, hc34, hlam, hphi, ht23, u2ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2332 | h2332
                  · linarith only [h1080, h1083, h2332, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2334 | h2334
                    · linarith only [h1080, h2087, h2334, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2336 | h2336
                      · linarith only [h2314, h2330, h2336, h655, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2338 | h2338
                        · linarith only [h1080, h1083, h2330, h2338, h884, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h1080, h1083, h2338, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h0, h1082, h2313, hlam]
        · linarith only [h0, h1082, h2312, hc24, hlam, hphi, u2ehi4]
      · linarith only [h0, h1080, h1083, h2311, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h999 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1080 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1081 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1082 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1083 | h1083
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h655 h884 h999 h1080 h1081 h1082 h1083
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h655 h884 h999 h1080 h1081 h1082 h1083

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h999 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1080 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1081 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1082 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h1081, h1082, hc25, hlam, hphi, u2ehi3]

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h999 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1080 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1081 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1082 | h1082
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h655 h884 h999 h1080 h1081 h1082
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h655 h884 h999 h1080 h1081 h1082

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h999 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1080 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1081 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h1080, h1081, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h999 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1080 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1081 | h1081
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0 m hb1 hb2 hb4 hb5 h0 h655 h884 h999 h1080 h1081
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x1 m hb1 hb2 hb4 hb5 h0 h655 h884 h999 h1080 h1081

end R2N4
