import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6419 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h6420 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6931 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h6933 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h6935 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h6937 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 1 3 5 (by decide) (by decide) with h6938 | h6938
  · rcases m.htr 1 4 5 (by decide) (by decide) with h6939 | h6939
    · linarith only [h2, h6420, h6939, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h6941 | h6941
      · rcases m.htr 2 3 5 (by decide) (by decide) with h6942 | h6942
        · rcases m.htr 2 4 5 (by decide) (by decide) with h6943 | h6943
          · rcases m.htr 3 4 5 (by decide) (by decide) with h6944 | h6944
            · linarith only [h2, h6420, h6937, h6944, hlam]
            · rcases h1bigk with h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c | h6946c
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                rcases p6946_3 (m.d 0 1) (by simp) with h6948 | h6948
                · rcases p6946_3 (m.d 1 2) (by simp) with h6949 | h6949
                  · linarith only [h6949, hlam, p6946_0]
                  · rcases p6946_3 (m.d 1 3) (by simp) with h6951 | h6951
                    · linarith only [h1, h6951, hlam]
                    · linarith only [h6931, h6951, hlam]
                · linarith only [h6948, hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h6938, hc01, hlam, hphi, ht0b, ht5b, p6946_1, u5ehi3]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                rcases p6946_3 (m.d 0 1) (by simp) with h6956 | h6956
                · rcases p6946_3 (m.d 1 2) (by simp) with h6957 | h6957
                  · linarith only [h0, h6957, hlam]
                  · rcases p6946_3 (m.d 1 3) (by simp) with h6959 | h6959
                    · linarith only [h1, h6959, hlam]
                    · linarith only [h6937, h6959, hlam]
                · linarith only [h6956, hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                rcases p6946_3 (m.d 0 1) (by simp) with h6963 | h6963
                · rcases p6946_3 (m.d 1 2) (by simp) with h6964 | h6964
                  · linarith only [h0, h6964, hlam]
                  · rcases p6946_3 (m.d 1 3) (by simp) with h6966 | h6966
                    · linarith only [h1, h6966, hlam]
                    · linarith only [h6938, h6966, hlam]
                · linarith only [h6963, hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h0, hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h6931, hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h6933, hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h6935, hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h1, hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                rcases p6946_3 (m.d 0 1) (by simp) with h6976 | h6976
                · rcases p6946_3 (m.d 1 2) (by simp) with h6977 | h6977
                  · linarith only [h6931, h6977, hlam]
                  · rcases p6946_3 (m.d 1 3) (by simp) with h6979 | h6979
                    · rcases p6946_3 (m.d 1 4) (by simp) with h6980 | h6980
                      · linarith only [h6937, h6980, hlam]
                      · linarith only [h6933, h6980, hlam]
                    · linarith only [h6931, h6979, hlam]
                · linarith only [h0, h6976, hlam]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                rcases p6946_3 (m.d 0 1) (by simp) with h6986 | h6986
                · rcases p6946_3 (m.d 1 2) (by simp) with h6987 | h6987
                  · linarith only [h6931, h6987, hlam]
                  · rcases p6946_3 (m.d 1 3) (by simp) with h6989 | h6989
                    · rcases p6946_3 (m.d 1 4) (by simp) with h6990 | h6990
                      · linarith only [h6937, h6990, hlam]
                      · rcases p6946_3 (m.d 1 5) (by simp) with h6992 | h6992
                        · linarith only [h6938, h6992, hlam]
                        · linarith only [h6939, h6992, hlam]
                    · linarith only [h6937, h6989, hlam]
                · linarith only [h2, h6986, hlam]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h1, h6938, hc01, hlam, hphi, ht0b, ht5b, p6946_1, u5ehi3]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h2, hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h2, h6420, h6941, h6943, hc12, hc23, hlam, hphi, p6946_1]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h6937, hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h6939, hlam, p6946_1]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h3, hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h3, h6420, h6941, h6943, hc12, hc23, hlam, hphi, p6946_1]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h6938, hlam, p6946_0]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [h3, h6420, h6933, h6941, h6943, hc12, hc23, hlam, hphi, p6946_1]
              · have p6946_0 := h6946c.1
                have p6946_1 := h6946c.2.1
                have p6946_2 := h6946c.2.2.1
                have p6946_3 := h6946c.2.2.2
                linarith only [hlam, p6946_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h7008 | h7008
            · linarith only [h2, h5543, h6937, h6943, h7008, hlam]
            · rcases h1bigk with h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c | h7010c
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                rcases p7010_3 (m.d 0 1) (by simp) with h7012 | h7012
                · rcases p7010_3 (m.d 1 2) (by simp) with h7013 | h7013
                  · linarith only [h7013, hlam, p7010_0]
                  · rcases p7010_3 (m.d 1 3) (by simp) with h7015 | h7015
                    · linarith only [h1, h7015, hlam]
                    · linarith only [h6931, h7015, hlam]
                · linarith only [h7012, hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [h6938, hc01, hlam, hphi, ht0b, ht5b, p7010_1, u5ehi3]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                rcases p7010_3 (m.d 0 1) (by simp) with h7020 | h7020
                · rcases p7010_3 (m.d 1 2) (by simp) with h7021 | h7021
                  · linarith only [h0, h7021, hlam]
                  · rcases p7010_3 (m.d 1 3) (by simp) with h7023 | h7023
                    · linarith only [h1, h7023, hlam]
                    · linarith only [h6937, h7023, hlam]
                · linarith only [h7020, hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                rcases p7010_3 (m.d 0 1) (by simp) with h7027 | h7027
                · rcases p7010_3 (m.d 1 2) (by simp) with h7028 | h7028
                  · linarith only [h0, h7028, hlam]
                  · rcases p7010_3 (m.d 1 3) (by simp) with h7030 | h7030
                    · linarith only [h1, h7030, hlam]
                    · linarith only [h6938, h7030, hlam]
                · linarith only [h7027, hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [h0, hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [h6931, hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [h6933, hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [h6935, hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [h1, hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                rcases p7010_3 (m.d 0 1) (by simp) with h7040 | h7040
                · rcases p7010_3 (m.d 1 2) (by simp) with h7041 | h7041
                  · linarith only [h6931, h7041, hlam]
                  · rcases p7010_3 (m.d 1 3) (by simp) with h7043 | h7043
                    · rcases p7010_3 (m.d 1 4) (by simp) with h7044 | h7044
                      · linarith only [h6937, h7044, hlam]
                      · linarith only [h6933, h7044, hlam]
                    · linarith only [h6931, h7043, hlam]
                · linarith only [h0, h7040, hlam]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                rcases p7010_3 (m.d 0 1) (by simp) with h7050 | h7050
                · rcases p7010_3 (m.d 1 2) (by simp) with h7051 | h7051
                  · linarith only [h6931, h7051, hlam]
                  · rcases p7010_3 (m.d 1 3) (by simp) with h7053 | h7053
                    · rcases p7010_3 (m.d 1 4) (by simp) with h7054 | h7054
                      · linarith only [h6937, h7054, hlam]
                      · rcases p7010_3 (m.d 1 5) (by simp) with h7056 | h7056
                        · linarith only [h6938, h7056, hlam]
                        · linarith only [h6939, h7056, hlam]
                    · linarith only [h6937, h7053, hlam]
                · linarith only [h2, h7050, hlam]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [h1, h6938, hc01, hlam, hphi, ht0b, ht5b, p7010_1, u5ehi3]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [h2, hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [h2, h5543, h6943, hc12, hc45, hlam, hphi, ht23, ht34, p7010_1]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [h6937, hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [h6939, hlam, p7010_1]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [h3, hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                rcases p7010_3 (m.d 0 1) (by simp) with h7068 | h7068
                · rcases p7010_3 (m.d 1 2) (by simp) with h7069 | h7069
                  · linarith only [h6935, h7069, hlam]
                  · rcases p7010_3 (m.d 1 3) (by simp) with h7071 | h7071
                    · rcases p7010_3 (m.d 1 4) (by simp) with h7072 | h7072
                      · linarith only [h6939, h7072, hlam]
                      · linarith only [h6933, h7072, hlam]
                    · linarith only [h6931, h7071, hlam]
                · linarith only [h0, h7068, hlam]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [h6938, hlam, p7010_0]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                rcases p7010_3 (m.d 0 1) (by simp) with h7078 | h7078
                · rcases p7010_3 (m.d 1 2) (by simp) with h7079 | h7079
                  · linarith only [h6935, h7079, hlam]
                  · rcases p7010_3 (m.d 1 3) (by simp) with h7081 | h7081
                    · rcases p7010_3 (m.d 1 4) (by simp) with h7082 | h7082
                      · linarith only [h6939, h7082, hlam]
                      · rcases p7010_3 (m.d 1 5) (by simp) with h7084 | h7084
                        · rcases h1emax with h7085 | h7085 | h7085 | h7085 | h7085
                          · linarith only [h1, h6933, h6938, h7085, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7010_1]
                          · rcases h3bigk with h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c | h7087c
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [hlam, p7087_0]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h4, h6933, h6938, hc12, hc23, hlam, hphi, p7010_1, p7087_1]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h4, hlam, p7087_1]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              rcases p7087_3 (m.d 0 3) (by simp) with h7091 | h7091
                              · rcases p7087_3 (m.d 1 3) (by simp) with h7092 | h7092
                                · linarith only [h1, h7092, hlam]
                                · linarith only [h6937, h7092, hlam]
                              · linarith only [h7091, hlam, p7087_0]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              rcases p7087_3 (m.d 0 3) (by simp) with h7096 | h7096
                              · rcases p7087_3 (m.d 1 3) (by simp) with h7097 | h7097
                                · linarith only [h1, h7097, hlam]
                                · linarith only [h6938, h7097, hlam]
                              · linarith only [h7096, hlam, p7087_0]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h1, hlam, p7087_0]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [hlam, p7087_0]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h6931, hlam, p7087_1]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              rcases p7087_3 (m.d 0 3) (by simp) with h7104 | h7104
                              · rcases p7087_3 (m.d 1 3) (by simp) with h7105 | h7105
                                · rcases p7087_3 (m.d 2 3) (by simp) with h7106 | h7106
                                  · rcases p7087_3 (m.d 3 4) (by simp) with h7107 | h7107
                                    · linarith only [h7107, hlam, p7087_0]
                                    · rcases p7087_3 (m.d 3 5) (by simp) with h7109 | h7109
                                      · linarith only [h6938, h7109, hlam]
                                      · linarith only [h7008, h7109, hlam]
                                  · linarith only [h6941, h7106, hlam]
                                · linarith only [h7105, hlam, p7087_0]
                              · linarith only [h6418, h7104, hlam]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p7087_1, u5ehi3]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h6419, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7087_1, u5ehi3]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h6938, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7087_1, u5ehi3]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [hlam, p7087_0]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              rcases p7087_3 (m.d 0 3) (by simp) with h7119 | h7119
                              · linarith only [h4, h7119, hlam]
                              · linarith only [h6418, h7119, hlam]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              rcases p7087_3 (m.d 0 3) (by simp) with h7122 | h7122
                              · linarith only [h4, h7122, hlam]
                              · linarith only [h6419, h7122, hlam]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h6418, hlam, p7087_0]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h6937, hlam, p7087_0]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h6941, hlam, p7087_0]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [hlam, p7087_0]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h7008, hlam, p7087_1]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h6419, hlam, p7087_0]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h6938, hlam, p7087_0]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h6942, hlam, p7087_0]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [h1, h6938, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7087_1]
                            · have p7087_0 := h7087c.1
                              have p7087_1 := h7087c.2.1
                              have p7087_2 := h7087c.2.2.1
                              have p7087_3 := h7087c.2.2.2
                              linarith only [hlam, p7087_0]
                          · linarith only [h6938, h7085, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases h3bigk with h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [hlam, p7136_0]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h6933, h6938, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7010_1, p7136_1]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h4, hlam, p7136_1]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              rcases p7136_3 (m.d 0 3) (by simp) with h7140 | h7140
                              · rcases p7136_3 (m.d 1 3) (by simp) with h7141 | h7141
                                · linarith only [h1, h7141, hlam]
                                · linarith only [h6937, h7141, hlam]
                              · linarith only [h7140, hlam, p7136_0]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              rcases p7136_3 (m.d 0 3) (by simp) with h7145 | h7145
                              · rcases p7136_3 (m.d 1 3) (by simp) with h7146 | h7146
                                · linarith only [h1, h7146, hlam]
                                · linarith only [h6938, h7146, hlam]
                              · linarith only [h7145, hlam, p7136_0]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h1, hlam, p7136_0]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [hlam, p7136_0]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h6931, hlam, p7136_1]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              rcases p7136_3 (m.d 0 3) (by simp) with h7153 | h7153
                              · rcases p7136_3 (m.d 1 3) (by simp) with h7154 | h7154
                                · rcases p7136_3 (m.d 2 3) (by simp) with h7155 | h7155
                                  · rcases p7136_3 (m.d 3 4) (by simp) with h7156 | h7156
                                    · linarith only [h7156, hlam, p7136_0]
                                    · rcases p7136_3 (m.d 3 5) (by simp) with h7158 | h7158
                                      · linarith only [h6938, h7158, hlam]
                                      · linarith only [h7008, h7158, hlam]
                                  · linarith only [h6941, h7155, hlam]
                                · linarith only [h7154, hlam, p7136_0]
                              · linarith only [h6418, h7153, hlam]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p7136_1, u5ehi3]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h6419, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7136_1, u5ehi3]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h6938, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7136_1, u5ehi3]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [hlam, p7136_0]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              rcases p7136_3 (m.d 0 3) (by simp) with h7168 | h7168
                              · linarith only [h4, h7168, hlam]
                              · linarith only [h6418, h7168, hlam]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              rcases p7136_3 (m.d 0 3) (by simp) with h7171 | h7171
                              · linarith only [h4, h7171, hlam]
                              · linarith only [h6419, h7171, hlam]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h6418, hlam, p7136_0]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h6937, hlam, p7136_0]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h6941, hlam, p7136_0]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [hlam, p7136_0]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h7008, hlam, p7136_1]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h6419, hlam, p7136_0]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h6938, hlam, p7136_0]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h6942, hlam, p7136_0]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [h1, h6938, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7136_1]
                            · have p7136_0 := h7136c.1
                              have p7136_1 := h7136c.2.1
                              have p7136_2 := h7136c.2.2.1
                              have p7136_3 := h7136c.2.2.2
                              linarith only [hlam, p7136_0]
                          · linarith only [h6933, h7085, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7010_1]
                        · linarith only [h6939, h7084, hlam]
                    · linarith only [h6937, h7081, hlam]
                · linarith only [h2, h7078, hlam]
              · have p7010_0 := h7010c.1
                have p7010_1 := h7010c.2.1
                have p7010_2 := h7010c.2.2.1
                have p7010_3 := h7010c.2.2.2
                linarith only [hlam, p7010_0]
        · linarith only [h0, h1, h4, h6938, h6942, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · linarith only [h4, h6418, h6941, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h7191 | h7191
    · linarith only [h2, h6419, h6420, h6937, h6938, h7191, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h7193 | h7193
      · rcases m.htr 2 3 5 (by decide) (by decide) with h7194 | h7194
        · rcases m.htr 2 4 5 (by decide) (by decide) with h7195 | h7195
          · rcases m.htr 3 4 5 (by decide) (by decide) with h7196 | h7196
            · linarith only [h5543, h6419, h6420, h6937, h6938, h7196, hc02, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h1bigk with h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                rcases p7198_3 (m.d 0 1) (by simp) with h7200 | h7200
                · rcases p7198_3 (m.d 1 2) (by simp) with h7201 | h7201
                  · linarith only [h7201, hlam, p7198_0]
                  · rcases p7198_3 (m.d 1 3) (by simp) with h7203 | h7203
                    · linarith only [h1, h7203, hlam]
                    · linarith only [h6931, h7203, hlam]
                · linarith only [h7200, hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                rcases p7198_3 (m.d 0 1) (by simp) with h7207 | h7207
                · rcases p7198_3 (m.d 1 2) (by simp) with h7208 | h7208
                  · linarith only [h0, h7208, hlam]
                  · rcases p7198_3 (m.d 1 3) (by simp) with h7210 | h7210
                    · linarith only [h7210, hlam, p7198_0]
                    · rcases p7198_3 (m.d 1 4) (by simp) with h7212 | h7212
                      · linarith only [h2, h7212, hlam]
                      · rcases p7198_3 (m.d 1 5) (by simp) with h7214 | h7214
                        · linarith only [h3, h7214, hlam]
                        · linarith only [h6938, h7214, hlam]
                · linarith only [h7207, hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                rcases p7198_3 (m.d 0 1) (by simp) with h7218 | h7218
                · rcases p7198_3 (m.d 1 2) (by simp) with h7219 | h7219
                  · linarith only [h0, h7219, hlam]
                  · rcases p7198_3 (m.d 1 3) (by simp) with h7221 | h7221
                    · linarith only [h1, h7221, hlam]
                    · linarith only [h6937, h7221, hlam]
                · linarith only [h7218, hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                rcases p7198_3 (m.d 0 1) (by simp) with h7225 | h7225
                · rcases p7198_3 (m.d 1 2) (by simp) with h7226 | h7226
                  · linarith only [h0, h7226, hlam]
                  · rcases p7198_3 (m.d 1 3) (by simp) with h7228 | h7228
                    · linarith only [h1, h7228, hlam]
                    · rcases p7198_3 (m.d 1 4) (by simp) with h7230 | h7230
                      · linarith only [h2, h7230, hlam]
                      · rcases p7198_3 (m.d 1 5) (by simp) with h7232 | h7232
                        · linarith only [h7232, hlam, p7198_0]
                        · rcases h1emax with h7234 | h7234 | h7234 | h7234 | h7234
                          · linarith only [h7234, hlam, hphi, ht01, ht0b, ht5b, p7198_1, u5ehi1]
                          · rcases h3bigk with h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [hlam, p7236_0]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              rcases p7236_3 (m.d 0 3) (by simp) with h7238 | h7238
                              · rcases p7236_3 (m.d 1 3) (by simp) with h7239 | h7239
                                · linarith only [h1, h7239, hlam]
                                · rcases p7236_3 (m.d 2 3) (by simp) with h7241 | h7241
                                  · rcases p7236_3 (m.d 3 4) (by simp) with h7242 | h7242
                                    · linarith only [h6418, h7242, hlam]
                                    · rcases p7236_3 (m.d 3 5) (by simp) with h7244 | h7244
                                      · linarith only [h6419, h7244, hlam]
                                      · linarith only [h6938, h7244, hlam]
                                  · linarith only [h6931, h7241, hlam]
                              · linarith only [h1, h7238, hlam]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h4, hlam, p7236_1]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h6419, h6937, h6938, hlam, p7236_2]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h1, h6937, h6938, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7236_1]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h1, hlam, p7236_0]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [hlam, p7236_0]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h6931, hlam, p7236_1]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h6419, h6420, h6938, hc34, hc45, hlam, hphi, p7236_1]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h6938, hlam, p7236_0]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h6419, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7236_1, u5ehi3]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              rcases p7236_3 (m.d 0 3) (by simp) with h7258 | h7258
                              · linarith only [h4, h7258, hlam]
                              · linarith only [h1, h7258, hlam]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [hlam, p7236_0]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h6419, h6420, h6937, h6938, h7193, h7195, hlam, p7236_2]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h6937, h6938, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7236_1]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h6418, hlam, p7236_0]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h6937, hlam, p7236_0]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h7193, hlam, p7236_0]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [hlam, p7236_0]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h7196, hlam, p7236_1]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h6419, hlam, p7236_0]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h6419, h6937, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7236_1]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [h7194, hlam, p7236_0]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              rcases p7236_3 (m.d 0 3) (by simp) with h7272 | h7272
                              · rcases p7236_3 (m.d 1 3) (by simp) with h7273 | h7273
                                · linarith only [h6938, h7273, hlam]
                                · linarith only [h6937, h7273, hlam]
                              · linarith only [h6418, h7272, hlam]
                            · have p7236_0 := h7236c.1
                              have p7236_1 := h7236c.2.1
                              have p7236_2 := h7236c.2.2.1
                              have p7236_3 := h7236c.2.2.2
                              linarith only [hlam, p7236_0]
                          · rcases h3bigk with h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c | h7278c
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [hlam, p7278_0]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              rcases p7278_3 (m.d 0 3) (by simp) with h7280 | h7280
                              · rcases p7278_3 (m.d 1 3) (by simp) with h7281 | h7281
                                · linarith only [h1, h7281, hlam]
                                · rcases p7278_3 (m.d 2 3) (by simp) with h7283 | h7283
                                  · rcases p7278_3 (m.d 3 4) (by simp) with h7284 | h7284
                                    · linarith only [h6418, h7284, hlam]
                                    · rcases p7278_3 (m.d 3 5) (by simp) with h7286 | h7286
                                      · linarith only [h6419, h7286, hlam]
                                      · linarith only [h6938, h7286, hlam]
                                  · linarith only [h6931, h7283, hlam]
                              · linarith only [h1, h7280, hlam]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h4, hlam, p7278_1]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h6419, h6937, h6938, hlam, p7278_2]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h6937, h6938, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7278_1]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h1, hlam, p7278_0]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [hlam, p7278_0]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h6931, hlam, p7278_1]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h4, h6419, h6938, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7278_1]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h6938, hlam, p7278_0]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h6419, h6938, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p7278_1]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              rcases p7278_3 (m.d 0 3) (by simp) with h7300 | h7300
                              · linarith only [h4, h7300, hlam]
                              · linarith only [h1, h7300, hlam]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [hlam, p7278_0]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h4, h6419, h6937, h6938, hlam, p7278_2]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h6937, h6938, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7278_1]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h6418, hlam, p7278_0]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h6937, hlam, p7278_0]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h7193, hlam, p7278_0]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [hlam, p7278_0]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h7196, hlam, p7278_1]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h6419, hlam, p7278_0]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h4, h6419, h6937, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7278_1]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [h7194, hlam, p7278_0]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              rcases p7278_3 (m.d 0 3) (by simp) with h7314 | h7314
                              · rcases p7278_3 (m.d 1 3) (by simp) with h7315 | h7315
                                · linarith only [h6938, h7315, hlam]
                                · linarith only [h6937, h7315, hlam]
                              · linarith only [h6418, h7314, hlam]
                            · have p7278_0 := h7278c.1
                              have p7278_1 := h7278c.2.1
                              have p7278_2 := h7278c.2.2.1
                              have p7278_3 := h7278c.2.2.2
                              linarith only [hlam, p7278_0]
                          · rcases h3bigk with h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c | h7320c
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [hlam, p7320_0]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              rcases p7320_3 (m.d 0 3) (by simp) with h7322 | h7322
                              · rcases p7320_3 (m.d 1 3) (by simp) with h7323 | h7323
                                · linarith only [h1, h7323, hlam]
                                · rcases p7320_3 (m.d 2 3) (by simp) with h7325 | h7325
                                  · rcases p7320_3 (m.d 3 4) (by simp) with h7326 | h7326
                                    · linarith only [h6418, h7326, hlam]
                                    · rcases p7320_3 (m.d 3 5) (by simp) with h7328 | h7328
                                      · linarith only [h6419, h7328, hlam]
                                      · linarith only [h6938, h7328, hlam]
                                  · linarith only [h6931, h7325, hlam]
                              · linarith only [h1, h7322, hlam]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h4, hlam, p7320_1]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h6419, h6937, h6938, hlam, p7320_2]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h6937, h6938, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7320_1]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h1, hlam, p7320_0]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [hlam, p7320_0]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h6931, hlam, p7320_1]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h4, h6419, h6938, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7320_1]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h6938, hlam, p7320_0]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h6419, h6938, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p7320_1]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              rcases p7320_3 (m.d 0 3) (by simp) with h7342 | h7342
                              · linarith only [h4, h7342, hlam]
                              · linarith only [h1, h7342, hlam]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [hlam, p7320_0]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h4, h6419, h6937, h6938, hlam, p7320_2]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h6937, h6938, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7320_1]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h6418, hlam, p7320_0]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h6937, hlam, p7320_0]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h7193, hlam, p7320_0]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [hlam, p7320_0]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h7196, hlam, p7320_1]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h6419, hlam, p7320_0]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h4, h6419, h6937, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7320_1]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [h7194, hlam, p7320_0]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              rcases p7320_3 (m.d 0 3) (by simp) with h7356 | h7356
                              · rcases p7320_3 (m.d 1 3) (by simp) with h7357 | h7357
                                · linarith only [h6938, h7357, hlam]
                                · linarith only [h6937, h7357, hlam]
                              · linarith only [h6418, h7356, hlam]
                            · have p7320_0 := h7320c.1
                              have p7320_1 := h7320c.2.1
                              have p7320_2 := h7320c.2.2.1
                              have p7320_3 := h7320c.2.2.2
                              linarith only [hlam, p7320_0]
                          · rcases h3bigk with h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c | h7362c
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [hlam, p7362_0]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              rcases p7362_3 (m.d 0 3) (by simp) with h7364 | h7364
                              · rcases p7362_3 (m.d 1 3) (by simp) with h7365 | h7365
                                · linarith only [h1, h7365, hlam]
                                · rcases p7362_3 (m.d 2 3) (by simp) with h7367 | h7367
                                  · rcases p7362_3 (m.d 3 4) (by simp) with h7368 | h7368
                                    · linarith only [h6418, h7368, hlam]
                                    · rcases p7362_3 (m.d 3 5) (by simp) with h7370 | h7370
                                      · linarith only [h6419, h7370, hlam]
                                      · linarith only [h6938, h7370, hlam]
                                  · linarith only [h6931, h7367, hlam]
                              · linarith only [h1, h7364, hlam]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h4, hlam, p7362_1]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h6419, h6937, h6938, hlam, p7362_2]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h6937, h6938, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7362_1]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h1, hlam, p7362_0]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [hlam, p7362_0]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h6931, hlam, p7362_1]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h4, h6419, h6938, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7362_1]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h6938, hlam, p7362_0]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h6419, h6938, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p7362_1]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              rcases p7362_3 (m.d 0 3) (by simp) with h7384 | h7384
                              · linarith only [h4, h7384, hlam]
                              · linarith only [h1, h7384, hlam]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [hlam, p7362_0]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h4, h6419, h6937, h6938, hlam, p7362_2]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h6937, h6938, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7362_1]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h6418, hlam, p7362_0]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h6937, hlam, p7362_0]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h7193, hlam, p7362_0]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [hlam, p7362_0]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h7196, hlam, p7362_1]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h6419, hlam, p7362_0]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h4, h6419, h6937, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7362_1]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [h7194, hlam, p7362_0]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              rcases p7362_3 (m.d 0 3) (by simp) with h7398 | h7398
                              · rcases p7362_3 (m.d 1 3) (by simp) with h7399 | h7399
                                · linarith only [h6938, h7399, hlam]
                                · linarith only [h6937, h7399, hlam]
                              · linarith only [h6418, h7398, hlam]
                            · have p7362_0 := h7362c.1
                              have p7362_1 := h7362c.2.1
                              have p7362_2 := h7362c.2.2.1
                              have p7362_3 := h7362c.2.2.2
                              linarith only [hlam, p7362_0]
                · linarith only [h7225, hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h0, hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h6931, hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h6933, hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h6935, hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h1, hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h6419, h6420, h6938, h7193, h7195, hc12, hc23, hlam, hphi, p7198_1]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h6419, h6420, h6933, h6938, h7193, h7195, hc12, hc23, hlam, hphi, p7198_1]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h6938, hlam, p7198_1]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h2, hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h2, h6420, h7193, h7195, hc12, hc23, hlam, hphi, p7198_1]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h6937, hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h7191, hlam, p7198_1]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h3, hlam, p7198_0]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h3, h6420, h7193, h7195, hc12, hc23, hlam, hphi, p7198_1]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h6419, h6420, h6931, h6938, h7193, h7195, hc12, hc23, hlam, hphi, p7198_1]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [h6419, h6420, h6933, h6938, h7193, h7195, hc12, hc23, hlam, hphi, p7198_1]
              · have p7198_0 := h7198c.1
                have p7198_1 := h7198c.2.1
                have p7198_2 := h7198c.2.2.1
                have p7198_3 := h7198c.2.2.2
                linarith only [hlam, p7198_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h7425 | h7425
            · linarith only [h1, h6937, h7195, h7425, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
            · rcases h1bigk with h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                rcases p7427_3 (m.d 0 1) (by simp) with h7429 | h7429
                · rcases p7427_3 (m.d 1 2) (by simp) with h7430 | h7430
                  · linarith only [h7430, hlam, p7427_0]
                  · rcases p7427_3 (m.d 1 3) (by simp) with h7432 | h7432
                    · linarith only [h1, h7432, hlam]
                    · linarith only [h6931, h7432, hlam]
                · linarith only [h7429, hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                rcases p7427_3 (m.d 0 1) (by simp) with h7436 | h7436
                · rcases p7427_3 (m.d 1 2) (by simp) with h7437 | h7437
                  · linarith only [h0, h7437, hlam]
                  · rcases p7427_3 (m.d 1 3) (by simp) with h7439 | h7439
                    · linarith only [h7439, hlam, p7427_0]
                    · rcases p7427_3 (m.d 1 4) (by simp) with h7441 | h7441
                      · linarith only [h2, h7441, hlam]
                      · rcases p7427_3 (m.d 1 5) (by simp) with h7443 | h7443
                        · linarith only [h3, h7443, hlam]
                        · linarith only [h6938, h7443, hlam]
                · linarith only [h7436, hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                rcases p7427_3 (m.d 0 1) (by simp) with h7447 | h7447
                · rcases p7427_3 (m.d 1 2) (by simp) with h7448 | h7448
                  · linarith only [h0, h7448, hlam]
                  · rcases p7427_3 (m.d 1 3) (by simp) with h7450 | h7450
                    · linarith only [h1, h7450, hlam]
                    · linarith only [h6937, h7450, hlam]
                · linarith only [h7447, hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                rcases p7427_3 (m.d 0 1) (by simp) with h7454 | h7454
                · rcases p7427_3 (m.d 1 2) (by simp) with h7455 | h7455
                  · linarith only [h0, h7455, hlam]
                  · rcases p7427_3 (m.d 1 3) (by simp) with h7457 | h7457
                    · linarith only [h1, h7457, hlam]
                    · rcases p7427_3 (m.d 1 4) (by simp) with h7459 | h7459
                      · linarith only [h2, h7459, hlam]
                      · rcases p7427_3 (m.d 1 5) (by simp) with h7461 | h7461
                        · linarith only [h7461, hlam, p7427_0]
                        · rcases h1emax with h7463 | h7463 | h7463 | h7463 | h7463
                          · linarith only [h7463, hlam, hphi, ht01, ht0b, ht5b, p7427_1, u5ehi1]
                          · rcases h3bigk with h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c | h7465c
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [hlam, p7465_0]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              rcases p7465_3 (m.d 0 3) (by simp) with h7467 | h7467
                              · rcases p7465_3 (m.d 1 3) (by simp) with h7468 | h7468
                                · linarith only [h1, h7468, hlam]
                                · rcases p7465_3 (m.d 2 3) (by simp) with h7470 | h7470
                                  · rcases p7465_3 (m.d 3 4) (by simp) with h7471 | h7471
                                    · linarith only [h6418, h7471, hlam]
                                    · rcases p7465_3 (m.d 3 5) (by simp) with h7473 | h7473
                                      · linarith only [h6419, h7473, hlam]
                                      · linarith only [h6938, h7473, hlam]
                                  · linarith only [h6931, h7470, hlam]
                              · linarith only [h1, h7467, hlam]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h4, hlam, p7465_1]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h6419, h6937, h6938, hlam, p7465_2]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h1, h6937, h6938, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7465_1]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h1, hlam, p7465_0]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [hlam, p7465_0]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h6931, hlam, p7465_1]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h6938, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7427_1, p7465_1]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h6938, hlam, p7465_0]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h6419, h6938, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p7465_1]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              rcases p7465_3 (m.d 0 3) (by simp) with h7487 | h7487
                              · linarith only [h4, h7487, hlam]
                              · linarith only [h1, h7487, hlam]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [hlam, p7465_0]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h4, h6419, h6937, h6938, hlam, p7465_2]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h6937, h6938, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7465_1]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h6418, hlam, p7465_0]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h6937, hlam, p7465_0]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h7193, hlam, p7465_0]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [hlam, p7465_0]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h7425, hlam, p7465_1]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h6419, hlam, p7465_0]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h6419, h6937, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7465_1]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [h7194, hlam, p7465_0]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              rcases p7465_3 (m.d 0 3) (by simp) with h7501 | h7501
                              · rcases p7465_3 (m.d 1 3) (by simp) with h7502 | h7502
                                · linarith only [h6938, h7502, hlam]
                                · linarith only [h6937, h7502, hlam]
                              · linarith only [h6418, h7501, hlam]
                            · have p7465_0 := h7465c.1
                              have p7465_1 := h7465c.2.1
                              have p7465_2 := h7465c.2.2.1
                              have p7465_3 := h7465c.2.2.2
                              linarith only [hlam, p7465_0]
                          · rcases h3bigk with h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c | h7507c
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [hlam, p7507_0]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              rcases p7507_3 (m.d 0 3) (by simp) with h7509 | h7509
                              · rcases p7507_3 (m.d 1 3) (by simp) with h7510 | h7510
                                · linarith only [h1, h7510, hlam]
                                · rcases p7507_3 (m.d 2 3) (by simp) with h7512 | h7512
                                  · rcases p7507_3 (m.d 3 4) (by simp) with h7513 | h7513
                                    · linarith only [h6418, h7513, hlam]
                                    · rcases p7507_3 (m.d 3 5) (by simp) with h7515 | h7515
                                      · linarith only [h6419, h7515, hlam]
                                      · linarith only [h6938, h7515, hlam]
                                  · linarith only [h6931, h7512, hlam]
                              · linarith only [h1, h7509, hlam]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h4, hlam, p7507_1]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h6419, h6937, h6938, hlam, p7507_2]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h6937, h6938, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7507_1]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h1, hlam, p7507_0]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [hlam, p7507_0]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h6931, hlam, p7507_1]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h6938, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7427_1, p7507_1]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h6938, hlam, p7507_0]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h6419, h6938, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p7507_1]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              rcases p7507_3 (m.d 0 3) (by simp) with h7529 | h7529
                              · linarith only [h4, h7529, hlam]
                              · linarith only [h1, h7529, hlam]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [hlam, p7507_0]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h4, h6419, h6937, h6938, hlam, p7507_2]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h6937, h6938, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7507_1]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h6418, hlam, p7507_0]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h6937, hlam, p7507_0]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h7193, hlam, p7507_0]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [hlam, p7507_0]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h7425, hlam, p7507_1]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h6419, hlam, p7507_0]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h6419, h6937, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7507_1]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [h7194, hlam, p7507_0]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              rcases p7507_3 (m.d 0 3) (by simp) with h7543 | h7543
                              · rcases p7507_3 (m.d 1 3) (by simp) with h7544 | h7544
                                · linarith only [h6938, h7544, hlam]
                                · linarith only [h6937, h7544, hlam]
                              · linarith only [h6418, h7543, hlam]
                            · have p7507_0 := h7507c.1
                              have p7507_1 := h7507c.2.1
                              have p7507_2 := h7507c.2.2.1
                              have p7507_3 := h7507c.2.2.2
                              linarith only [hlam, p7507_0]
                          · rcases h3bigk with h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c | h7549c
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [hlam, p7549_0]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              rcases p7549_3 (m.d 0 3) (by simp) with h7551 | h7551
                              · rcases p7549_3 (m.d 1 3) (by simp) with h7552 | h7552
                                · linarith only [h1, h7552, hlam]
                                · rcases p7549_3 (m.d 2 3) (by simp) with h7554 | h7554
                                  · rcases p7549_3 (m.d 3 4) (by simp) with h7555 | h7555
                                    · linarith only [h6418, h7555, hlam]
                                    · rcases p7549_3 (m.d 3 5) (by simp) with h7557 | h7557
                                      · linarith only [h6419, h7557, hlam]
                                      · linarith only [h6938, h7557, hlam]
                                  · linarith only [h6931, h7554, hlam]
                              · linarith only [h1, h7551, hlam]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h4, hlam, p7549_1]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h6419, h6937, h6938, hlam, p7549_2]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h4, h6937, h6938, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7549_1]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h1, hlam, p7549_0]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [hlam, p7549_0]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h6931, hlam, p7549_1]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h4, h6419, h6938, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7549_1]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h6938, hlam, p7549_0]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h6419, h6938, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p7549_1]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              rcases p7549_3 (m.d 0 3) (by simp) with h7571 | h7571
                              · linarith only [h4, h7571, hlam]
                              · linarith only [h1, h7571, hlam]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [hlam, p7549_0]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h4, h6419, h6937, h6938, hlam, p7549_2]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h6937, h6938, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7549_1]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h6418, hlam, p7549_0]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h6937, hlam, p7549_0]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h7193, hlam, p7549_0]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [hlam, p7549_0]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h7425, hlam, p7549_1]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h6419, hlam, p7549_0]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h6419, h6937, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7549_1]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [h7194, hlam, p7549_0]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              rcases p7549_3 (m.d 0 3) (by simp) with h7585 | h7585
                              · rcases p7549_3 (m.d 1 3) (by simp) with h7586 | h7586
                                · linarith only [h6938, h7586, hlam]
                                · linarith only [h6937, h7586, hlam]
                              · linarith only [h6418, h7585, hlam]
                            · have p7549_0 := h7549c.1
                              have p7549_1 := h7549c.2.1
                              have p7549_2 := h7549c.2.2.1
                              have p7549_3 := h7549c.2.2.2
                              linarith only [hlam, p7549_0]
                          · rcases h3bigk with h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c | h7591c
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [hlam, p7591_0]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              rcases p7591_3 (m.d 0 3) (by simp) with h7593 | h7593
                              · rcases p7591_3 (m.d 1 3) (by simp) with h7594 | h7594
                                · linarith only [h1, h7594, hlam]
                                · rcases p7591_3 (m.d 2 3) (by simp) with h7596 | h7596
                                  · rcases p7591_3 (m.d 3 4) (by simp) with h7597 | h7597
                                    · linarith only [h6418, h7597, hlam]
                                    · rcases p7591_3 (m.d 3 5) (by simp) with h7599 | h7599
                                      · linarith only [h6419, h7599, hlam]
                                      · linarith only [h6938, h7599, hlam]
                                  · linarith only [h6931, h7596, hlam]
                              · linarith only [h1, h7593, hlam]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h4, hlam, p7591_1]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h6419, h6937, h6938, hlam, p7591_2]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h6937, h6938, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7591_1]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h1, hlam, p7591_0]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [hlam, p7591_0]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h6931, hlam, p7591_1]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h6938, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7427_1, p7591_1]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h6938, hlam, p7591_0]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h6419, h6938, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p7591_1]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              rcases p7591_3 (m.d 0 3) (by simp) with h7613 | h7613
                              · linarith only [h4, h7613, hlam]
                              · linarith only [h1, h7613, hlam]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [hlam, p7591_0]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h4, h6419, h6937, h6938, hlam, p7591_2]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h6937, h6938, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7591_1]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h6418, hlam, p7591_0]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h6937, hlam, p7591_0]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h7193, hlam, p7591_0]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [hlam, p7591_0]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h7425, hlam, p7591_1]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h6419, hlam, p7591_0]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h6419, h6937, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7591_1]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [h7194, hlam, p7591_0]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              rcases p7591_3 (m.d 0 3) (by simp) with h7627 | h7627
                              · rcases p7591_3 (m.d 1 3) (by simp) with h7628 | h7628
                                · linarith only [h6938, h7628, hlam]
                                · linarith only [h6937, h7628, hlam]
                              · linarith only [h6418, h7627, hlam]
                            · have p7591_0 := h7591c.1
                              have p7591_1 := h7591c.2.1
                              have p7591_2 := h7591c.2.2.1
                              have p7591_3 := h7591c.2.2.2
                              linarith only [hlam, p7591_0]
                · linarith only [h7454, hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h0, hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h6931, hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h6933, hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h6935, hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h1, hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h4, h6419, h6938, hc12, hc23, hlam, hphi, p7427_1]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h4, h6419, h6933, h6938, hc12, hc23, hlam, hphi, p7427_1]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h6938, hlam, p7427_1]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h2, hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h2, h5543, h7195, hc12, hc45, hlam, hphi, ht23, ht34, p7427_1]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h6937, hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h7191, hlam, p7427_1]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h3, hlam, p7427_0]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h4, h6419, h6938, hc12, hc23, hlam, hphi, p7427_1]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h4, h6419, h6931, h6938, hc12, hc23, hlam, hphi, p7427_1]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [h4, h6419, h6933, h6938, hc12, hc23, hlam, hphi, p7427_1]
              · have p7427_0 := h7427c.1
                have p7427_1 := h7427c.2.1
                have p7427_2 := h7427c.2.2.1
                have p7427_3 := h7427c.2.2.2
                linarith only [hlam, p7427_0]
        · linarith only [h4, h6419, h7194, hlam]
      · linarith only [h4, h6419, h6937, h6938, h7193, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]

end R2N4
