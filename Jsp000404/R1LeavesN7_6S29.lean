import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12982000 in
set_option maxHeartbeats 12982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s10_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10058 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h10059 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  rcases m.htr 0 2 3 (by decide) (by decide) with h10060 | h10060
  · rcases m.htr 0 2 4 (by decide) (by decide) with h10061 | h10061
    · rcases m.htr 0 2 5 (by decide) (by decide) with h10062 | h10062
      · rcases m.htr 0 3 4 (by decide) (by decide) with h10063 | h10063
        · rcases m.htr 0 3 5 (by decide) (by decide) with h10064 | h10064
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10065 | h10065
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10066 | h10066
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10067 | h10067
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10068 | h10068
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10069 | h10069
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10070 | h10070
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10071 | h10071
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10072 | h10072
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10073 | h10073
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10074 | h10074
                              · linarith only [h10060, h10071, h10074, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h10058, h10060, h10070, h10074, h6793, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h10058, h10060, h10070, h10073, h6793, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h10060, h10064, h10071, h10072, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10079 | h10079
                          · linarith only [h10058, h10060, h10069, h10071, h10079, h6793, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10081 | h10081
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10082 | h10082
                              · rcases h0bigk with h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [hlam, p10083_0]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h0, hlam, p10083_1]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h6793, hlam, p10083_0]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10058, h10060, h10069, h10079, h10082, h6793, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10083_1, u0elo1]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10060, h10064, h10079, h6793, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10083_1, u0elo1]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10058, h10069, h10079, h10082, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10083_1, u0elo1]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [hlam, p10083_0]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10058, h10069, h10079, h10082, h6793, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10083_1, u0elo1]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10058, h10069, h10079, h10082, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10083_1, u0elo1]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10064, h10079, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10083_1, u0elo1]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10058, h10069, h10079, h10082, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10083_1, u0elo2]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10060, hlam, p10083_1]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [hlam, p10083_0]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10058, h10060, h10069, h10079, h10082, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10083_1, u0elo1]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10060, h10064, h10079, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10083_1, u0elo1]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10058, hlam, p10083_0]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10061, hlam, p10083_0]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10063, hlam, p10083_0]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [hlam, p10083_0]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10064, h10079, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10083_1, u0elo3]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10059, hlam, p10083_0]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10062, hlam, p10083_1]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10064, hlam, p10083_0]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [h10065, hlam, p10083_1]
                                · have p10083_0 := h10083c.1
                                  have p10083_1 := h10083c.2.1
                                  have p10083_2 := h10083c.2.2.1
                                  have p10083_3 := h10083c.2.2.2
                                  linarith only [hlam, p10083_0]
                              · linarith only [h10058, h10060, h10070, h10071, h10082, h6793, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h10058, h10060, h10070, h10071, h10081, h6793, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10111 | h10111
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10112 | h10112
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10113 | h10113
                            · linarith only [h10067, h10070, h10113, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10115 | h10115
                              · linarith only [h10067, h10070, h10111, h10115, hlam]
                              · rcases h0bigk with h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c | h10117c
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [hlam, p10117_0]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h0, hlam, p10117_1]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h6793, hlam, p10117_0]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10060, h10065, h10067, h10070, h10111, h6793, hc34, hlam, hphi, ht0b, ht45, ht5b, p10117_1, u0elo1]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10060, h10065, h10067, h10070, h10111, h6793, hc34, hlam, hphi, ht0b, ht45, ht5b, p10117_1, u0elo1]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10058, h10067, h10111, hc34, hlam, hphi, ht0b, ht45, ht5b, p10117_1, u0elo1]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [hlam, p10117_0]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10058, h10067, h10111, h6793, hc34, hlam, hphi, ht0b, ht45, ht5b, p10117_1, u0elo1]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10065, h10067, h10070, h10111, hc34, hlam, hphi, ht0b, ht45, ht5b, p10117_1, u0elo1]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10065, h10067, h10070, h10111, hc34, hlam, hphi, ht0b, ht45, ht5b, p10117_1, u0elo1]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10058, h10065, h10067, h10070, h10111, hc34, hlam, hphi, ht0b, ht45, ht5b, p10117_1, u0elo2]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10060, hlam, p10117_1]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [hlam, p10117_0]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10060, h10065, h10067, h10070, h10111, hc34, hlam, hphi, ht0b, ht45, ht5b, p10117_1, u0elo1]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10060, h10065, h10067, h10070, h10111, hc34, hlam, hphi, ht0b, ht45, ht5b, p10117_1, u0elo1]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10058, hlam, p10117_0]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10061, hlam, p10117_0]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10063, hlam, p10117_0]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [hlam, p10117_0]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10058, h10065, h10067, h10070, h10111, hc34, hlam, hphi, ht0b, ht45, ht5b, p10117_1, u0elo0]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10059, hlam, p10117_0]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10062, hlam, p10117_1]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10064, hlam, p10117_0]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [h10065, hlam, p10117_1]
                                · have p10117_0 := h10117c.1
                                  have p10117_1 := h10117c.2.1
                                  have p10117_2 := h10117c.2.2.1
                                  have p10117_3 := h10117c.2.2.2
                                  linarith only [hlam, p10117_0]
                          · linarith only [h10060, h10064, h10111, h10112, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h10058, h10065, h10066, h10069, h10070, h10111, h6793, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h10063, h10069, h6793, hlam]
                  · linarith only [h0, h10062, h10068, hlam]
                · linarith only [h0, h10061, h10067, hlam]
              · linarith only [h0, h10060, h10066, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10149 | h10149
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10150 | h10150
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10151 | h10151
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10152 | h10152
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10153 | h10153
                      · linarith only [h10058, h10065, h10153, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10155 | h10155
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10156 | h10156
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10157 | h10157
                            · linarith only [h10058, h10065, h10150, h10157, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10159 | h10159
                              · linarith only [h10060, h10065, h10155, h10159, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases h0bigk with h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c | h10161c
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [hlam, p10161_0]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [h0, hlam, p10161_1]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [h6793, hlam, p10161_0]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  rcases p10161_3 (m.d 0 1) (by simp) with h10165 | h10165
                                  · rcases p10161_3 (m.d 0 2) (by simp) with h10166 | h10166
                                    · rcases p10161_3 (m.d 0 3) (by simp) with h10167 | h10167
                                      · rcases p10161_3 (m.d 0 4) (by simp) with h10168 | h10168
                                        · linarith only [h10058, h10168, hlam]
                                        · rcases p10161_3 (m.d 0 5) (by simp) with h10170 | h10170
                                          · linarith only [h10059, h10170, hlam]
                                          · linarith only [h10065, h10170, hlam]
                                      · linarith only [h10063, h10167, hlam]
                                    · linarith only [h10061, h10166, hlam]
                                  · linarith only [h10058, h10165, hlam]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  rcases p10161_3 (m.d 0 1) (by simp) with h10176 | h10176
                                  · rcases p10161_3 (m.d 0 2) (by simp) with h10177 | h10177
                                    · rcases p10161_3 (m.d 0 3) (by simp) with h10178 | h10178
                                      · rcases p10161_3 (m.d 0 4) (by simp) with h10179 | h10179
                                        · linarith only [h10058, h10179, hlam]
                                        · rcases p10161_3 (m.d 0 5) (by simp) with h10181 | h10181
                                          · linarith only [h10059, h10181, hlam]
                                          · rcases h0emin with h10183 | h10183 | h10183 | h10183 | h10183
                                            · rcases h2bigk with h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [hlam, p10184_0]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h0, hlam, p10184_1]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10184_1, u0elo1]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                rcases p10184_3 (m.d 0 2) (by simp) with h10188 | h10188
                                                · rcases p10184_3 (m.d 1 2) (by simp) with h10189 | h10189
                                                  · rcases p10184_3 (m.d 2 3) (by simp) with h10190 | h10190
                                                    · linarith only [h10060, h10190, hlam]
                                                    · linarith only [h10155, h10190, hlam]
                                                  · linarith only [h10150, h10189, hlam]
                                                · linarith only [h10188, hlam, p10184_0]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                rcases p10184_3 (m.d 0 2) (by simp) with h10195 | h10195
                                                · rcases p10184_3 (m.d 1 2) (by simp) with h10196 | h10196
                                                  · rcases p10184_3 (m.d 2 3) (by simp) with h10197 | h10197
                                                    · linarith only [h10060, h10197, hlam]
                                                    · linarith only [h10156, h10197, hlam]
                                                  · linarith only [h10151, h10196, hlam]
                                                · linarith only [h10195, hlam, p10184_0]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h0, h10183, hc12, hlam, ht01, p10184_1]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [hlam, p10184_0]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                rcases p10184_3 (m.d 0 2) (by simp) with h10204 | h10204
                                                · linarith only [h0, h10204, hlam]
                                                · linarith only [h10060, h10204, hlam]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h0, h10058, h10065, h10150, hlam, p10161_1, p10184_2]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10062, h10149, h6793, hlam, p10161_1, p10184_2]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10060, hlam, p10184_0]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10149, hlam, p10184_0]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [hlam, p10184_0]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10060, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10184_1, u0elo1]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10060, hc25, hlam, hphi, ht0b, ht5b, p10184_1, u0elo1]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10061, hlam, p10184_0]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10150, hlam, p10184_0]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10155, hlam, p10184_1]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [hlam, p10184_0]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10157, hlam, p10184_1]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10062, hlam, p10184_0]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10151, hlam, p10184_0]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10156, hlam, p10184_1]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [h10062, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10184_1, u0elo1]
                                              · have p10184_0 := h10184c.1
                                                have p10184_1 := h10184c.2.1
                                                have p10184_2 := h10184c.2.2.1
                                                have p10184_3 := h10184c.2.2.2
                                                linarith only [hlam, p10184_0]
                                            · rcases h2bigk with h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c | h10224c
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [hlam, p10224_0]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h0, hlam, p10224_1]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10224_1, u0elo1]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                rcases p10224_3 (m.d 0 2) (by simp) with h10228 | h10228
                                                · rcases p10224_3 (m.d 1 2) (by simp) with h10229 | h10229
                                                  · rcases p10224_3 (m.d 2 3) (by simp) with h10230 | h10230
                                                    · linarith only [h10060, h10230, hlam]
                                                    · linarith only [h10155, h10230, hlam]
                                                  · linarith only [h10150, h10229, hlam]
                                                · linarith only [h10228, hlam, p10224_0]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                rcases p10224_3 (m.d 0 2) (by simp) with h10235 | h10235
                                                · rcases p10224_3 (m.d 1 2) (by simp) with h10236 | h10236
                                                  · rcases p10224_3 (m.d 2 3) (by simp) with h10237 | h10237
                                                    · linarith only [h10060, h10237, hlam]
                                                    · linarith only [h10156, h10237, hlam]
                                                  · linarith only [h10151, h10236, hlam]
                                                · linarith only [h10235, hlam, p10224_0]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10183, hc12, hlam, ht01, p10224_1]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [hlam, p10224_0]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                rcases p10224_3 (m.d 0 2) (by simp) with h10244 | h10244
                                                · linarith only [h0, h10244, hlam]
                                                · linarith only [h10060, h10244, hlam]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h0, h10058, h10065, h10150, hlam, p10161_1, p10224_2]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10059, h10149, h10151, h6793, hlam, p10161_1, p10224_2]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10060, hlam, p10224_0]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10149, hlam, p10224_0]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [hlam, p10224_0]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10060, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10224_1, u0elo1]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10060, hc25, hlam, hphi, ht0b, ht5b, p10224_1, u0elo1]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10061, hlam, p10224_0]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10150, hlam, p10224_0]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10155, hlam, p10224_1]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [hlam, p10224_0]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10157, hlam, p10224_1]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10062, hlam, p10224_0]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10151, hlam, p10224_0]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10156, hlam, p10224_1]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [h10062, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10224_1, u0elo1]
                                              · have p10224_0 := h10224c.1
                                                have p10224_1 := h10224c.2.1
                                                have p10224_2 := h10224c.2.2.1
                                                have p10224_3 := h10224c.2.2.2
                                                linarith only [hlam, p10224_0]
                                            · rcases h2bigk with h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c | h10264c
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [hlam, p10264_0]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h0, hlam, p10264_1]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10264_1, u0elo1]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                rcases p10264_3 (m.d 0 2) (by simp) with h10268 | h10268
                                                · rcases p10264_3 (m.d 1 2) (by simp) with h10269 | h10269
                                                  · rcases p10264_3 (m.d 2 3) (by simp) with h10270 | h10270
                                                    · linarith only [h10060, h10270, hlam]
                                                    · linarith only [h10155, h10270, hlam]
                                                  · linarith only [h10150, h10269, hlam]
                                                · linarith only [h10268, hlam, p10264_0]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                rcases p10264_3 (m.d 0 2) (by simp) with h10275 | h10275
                                                · rcases p10264_3 (m.d 1 2) (by simp) with h10276 | h10276
                                                  · rcases p10264_3 (m.d 2 3) (by simp) with h10277 | h10277
                                                    · linarith only [h10060, h10277, hlam]
                                                    · linarith only [h10156, h10277, hlam]
                                                  · linarith only [h10151, h10276, hlam]
                                                · linarith only [h10275, hlam, p10264_0]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h0, h10058, h10065, h10150, h10155, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10161_1, p10264_1]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [hlam, p10264_0]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                rcases p10264_3 (m.d 0 2) (by simp) with h10284 | h10284
                                                · linarith only [h0, h10284, hlam]
                                                · linarith only [h10060, h10284, hlam]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h0, h10058, h10065, h10150, hlam, p10161_1, p10264_2]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10059, h10149, h10151, h6793, hlam, p10161_1, p10264_2]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10060, hlam, p10264_0]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10149, hlam, p10264_0]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [hlam, p10264_0]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10060, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10264_1, u0elo1]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10060, hc25, hlam, hphi, ht0b, ht5b, p10264_1, u0elo1]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10061, hlam, p10264_0]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10150, hlam, p10264_0]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10155, hlam, p10264_1]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [hlam, p10264_0]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10157, hlam, p10264_1]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10062, hlam, p10264_0]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10151, hlam, p10264_0]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10156, hlam, p10264_1]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [h10062, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10264_1, u0elo1]
                                              · have p10264_0 := h10264c.1
                                                have p10264_1 := h10264c.2.1
                                                have p10264_2 := h10264c.2.2.1
                                                have p10264_3 := h10264c.2.2.2
                                                linarith only [hlam, p10264_0]
                                            · linarith only [h10065, h10183, hlam, p10161_1, u0elo0]
                                            · linarith only [h10183, h6793, hlam, p10161_1, u0elo2]
                                      · linarith only [h10064, h10178, hlam]
                                    · linarith only [h10062, h10177, hlam]
                                  · linarith only [h10059, h10176, hlam]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [h10058, h10150, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10161_1, u0elo1]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [hlam, p10161_0]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [h10058, h10150, h10155, h6793, hc34, hlam, hphi, ht0b, ht45, ht5b, p10161_1, u0elo1]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  rcases p10161_3 (m.d 0 1) (by simp) with h10312 | h10312
                                  · linarith only [h0, h10312, hlam]
                                  · linarith only [h10058, h10312, hlam]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  rcases p10161_3 (m.d 0 1) (by simp) with h10315 | h10315
                                  · linarith only [h0, h10315, hlam]
                                  · linarith only [h10059, h10315, hlam]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [h10059, h10150, h10153, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10161_1, u0elo2]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [h10060, hlam, p10161_1]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [hlam, p10161_0]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  rcases p10161_3 (m.d 0 1) (by simp) with h10321 | h10321
                                  · linarith only [h10321, h6793, hlam]
                                  · linarith only [h10058, h10321, hlam]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  rcases p10161_3 (m.d 0 1) (by simp) with h10324 | h10324
                                  · linarith only [h10324, h6793, hlam]
                                  · linarith only [h10059, h10324, hlam]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [h10058, hlam, p10161_0]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [h10061, hlam, p10161_0]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [h10063, hlam, p10161_0]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [hlam, p10161_0]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [h10065, hlam, p10161_0]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [h10059, hlam, p10161_0]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [h10062, hlam, p10161_1]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [h10064, hlam, p10161_0]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  rcases p10161_3 (m.d 0 1) (by simp) with h10335 | h10335
                                  · rcases p10161_3 (m.d 0 2) (by simp) with h10336 | h10336
                                    · rcases p10161_3 (m.d 0 3) (by simp) with h10337 | h10337
                                      · rcases p10161_3 (m.d 0 4) (by simp) with h10338 | h10338
                                        · linarith only [h10065, h10338, hlam]
                                        · rcases p10161_3 (m.d 0 5) (by simp) with h10340 | h10340
                                          · rcases h0emin with h10341 | h10341 | h10341 | h10341 | h10341
                                            · rcases h2bigk with h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c | h10342c
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [hlam, p10342_0]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h0, hlam, p10342_1]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10342_1, u0elo1]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                rcases p10342_3 (m.d 0 2) (by simp) with h10346 | h10346
                                                · rcases p10342_3 (m.d 1 2) (by simp) with h10347 | h10347
                                                  · rcases p10342_3 (m.d 2 3) (by simp) with h10348 | h10348
                                                    · linarith only [h10060, h10348, hlam]
                                                    · linarith only [h10155, h10348, hlam]
                                                  · linarith only [h10150, h10347, hlam]
                                                · linarith only [h10346, hlam, p10342_0]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                rcases p10342_3 (m.d 0 2) (by simp) with h10353 | h10353
                                                · rcases p10342_3 (m.d 1 2) (by simp) with h10354 | h10354
                                                  · rcases p10342_3 (m.d 2 3) (by simp) with h10355 | h10355
                                                    · linarith only [h10060, h10355, hlam]
                                                    · linarith only [h10156, h10355, hlam]
                                                  · linarith only [h10151, h10354, hlam]
                                                · linarith only [h10353, hlam, p10342_0]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h0, h10058, h10059, h10150, h10155, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10161_1, p10342_1]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [hlam, p10342_0]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                rcases p10342_3 (m.d 0 2) (by simp) with h10362 | h10362
                                                · linarith only [h0, h10362, hlam]
                                                · linarith only [h10060, h10362, hlam]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h0, h10058, h10059, h10150, hlam, p10161_1, p10342_2]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                rcases p10342_3 (m.d 0 2) (by simp) with h10366 | h10366
                                                · linarith only [h0, h10366, hlam]
                                                · linarith only [h10062, h10366, hlam]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h10060, hlam, p10342_0]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h10149, hlam, p10342_0]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [hlam, p10342_0]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h10060, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10342_1, u0elo1]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h10060, hc25, hlam, hphi, ht0b, ht5b, p10342_1, u0elo1]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h10061, hlam, p10342_0]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h10150, hlam, p10342_0]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h10155, hlam, p10342_1]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [hlam, p10342_0]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h10157, hlam, p10342_1]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h10062, hlam, p10342_0]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h10151, hlam, p10342_0]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h10156, hlam, p10342_1]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [h10062, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10342_1, u0elo1]
                                              · have p10342_0 := h10342c.1
                                                have p10342_1 := h10342c.2.1
                                                have p10342_2 := h10342c.2.2.1
                                                have p10342_3 := h10342c.2.2.2
                                                linarith only [hlam, p10342_0]
                                            · rcases h2bigk with h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c | h10384c
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [hlam, p10384_0]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h0, hlam, p10384_1]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10384_1, u0elo1]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                rcases p10384_3 (m.d 0 2) (by simp) with h10388 | h10388
                                                · rcases p10384_3 (m.d 1 2) (by simp) with h10389 | h10389
                                                  · rcases p10384_3 (m.d 2 3) (by simp) with h10390 | h10390
                                                    · linarith only [h10060, h10390, hlam]
                                                    · linarith only [h10155, h10390, hlam]
                                                  · linarith only [h10150, h10389, hlam]
                                                · linarith only [h10388, hlam, p10384_0]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                rcases p10384_3 (m.d 0 2) (by simp) with h10395 | h10395
                                                · rcases p10384_3 (m.d 1 2) (by simp) with h10396 | h10396
                                                  · rcases p10384_3 (m.d 2 3) (by simp) with h10397 | h10397
                                                    · linarith only [h10060, h10397, hlam]
                                                    · linarith only [h10156, h10397, hlam]
                                                  · linarith only [h10151, h10396, hlam]
                                                · linarith only [h10395, hlam, p10384_0]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10341, hc12, hlam, ht01, p10384_1]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [hlam, p10384_0]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                rcases p10384_3 (m.d 0 2) (by simp) with h10404 | h10404
                                                · linarith only [h0, h10404, hlam]
                                                · linarith only [h10060, h10404, hlam]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h0, h10058, h10059, h10150, hlam, p10161_1, p10384_2]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                rcases p10384_3 (m.d 0 2) (by simp) with h10408 | h10408
                                                · linarith only [h0, h10408, hlam]
                                                · linarith only [h10062, h10408, hlam]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10060, hlam, p10384_0]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10149, hlam, p10384_0]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [hlam, p10384_0]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10060, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10384_1, u0elo1]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10060, hc25, hlam, hphi, ht0b, ht5b, p10384_1, u0elo1]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10061, hlam, p10384_0]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10150, hlam, p10384_0]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10155, hlam, p10384_1]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [hlam, p10384_0]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10157, hlam, p10384_1]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10062, hlam, p10384_0]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10151, hlam, p10384_0]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10156, hlam, p10384_1]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [h10062, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10384_1, u0elo1]
                                              · have p10384_0 := h10384c.1
                                                have p10384_1 := h10384c.2.1
                                                have p10384_2 := h10384c.2.2.1
                                                have p10384_3 := h10384c.2.2.2
                                                linarith only [hlam, p10384_0]
                                            · rcases h2bigk with h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c | h10426c
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [hlam, p10426_0]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h0, hlam, p10426_1]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10426_1, u0elo1]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                rcases p10426_3 (m.d 0 2) (by simp) with h10430 | h10430
                                                · rcases p10426_3 (m.d 1 2) (by simp) with h10431 | h10431
                                                  · rcases p10426_3 (m.d 2 3) (by simp) with h10432 | h10432
                                                    · linarith only [h10060, h10432, hlam]
                                                    · linarith only [h10155, h10432, hlam]
                                                  · linarith only [h10150, h10431, hlam]
                                                · linarith only [h10430, hlam, p10426_0]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                rcases p10426_3 (m.d 0 2) (by simp) with h10437 | h10437
                                                · rcases p10426_3 (m.d 1 2) (by simp) with h10438 | h10438
                                                  · rcases p10426_3 (m.d 2 3) (by simp) with h10439 | h10439
                                                    · linarith only [h10060, h10439, hlam]
                                                    · linarith only [h10156, h10439, hlam]
                                                  · linarith only [h10151, h10438, hlam]
                                                · linarith only [h10437, hlam, p10426_0]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h0, h10058, h10059, h10150, h10155, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10161_1, p10426_1]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [hlam, p10426_0]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                rcases p10426_3 (m.d 0 2) (by simp) with h10446 | h10446
                                                · linarith only [h0, h10446, hlam]
                                                · linarith only [h10060, h10446, hlam]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h0, h10058, h10059, h10150, hlam, p10161_1, p10426_2]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                rcases p10426_3 (m.d 0 2) (by simp) with h10450 | h10450
                                                · linarith only [h0, h10450, hlam]
                                                · linarith only [h10062, h10450, hlam]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h10060, hlam, p10426_0]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h10149, hlam, p10426_0]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [hlam, p10426_0]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h10060, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10426_1, u0elo1]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h10060, hc25, hlam, hphi, ht0b, ht5b, p10426_1, u0elo1]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h10061, hlam, p10426_0]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h10150, hlam, p10426_0]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h10155, hlam, p10426_1]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [hlam, p10426_0]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h10157, hlam, p10426_1]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h10062, hlam, p10426_0]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h10151, hlam, p10426_0]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h10156, hlam, p10426_1]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [h10062, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10426_1, u0elo1]
                                              · have p10426_0 := h10426c.1
                                                have p10426_1 := h10426c.2.1
                                                have p10426_2 := h10426c.2.2.1
                                                have p10426_3 := h10426c.2.2.2
                                                linarith only [hlam, p10426_0]
                                            · linarith only [h10059, h10341, hlam, p10161_1, u0elo0]
                                            · rcases h2bigk with h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c | h10469c
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [hlam, p10469_0]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h0, hlam, p10469_1]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10469_1, u0elo1]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                rcases p10469_3 (m.d 0 2) (by simp) with h10473 | h10473
                                                · rcases p10469_3 (m.d 1 2) (by simp) with h10474 | h10474
                                                  · rcases p10469_3 (m.d 2 3) (by simp) with h10475 | h10475
                                                    · linarith only [h10060, h10475, hlam]
                                                    · linarith only [h10155, h10475, hlam]
                                                  · linarith only [h10150, h10474, hlam]
                                                · linarith only [h10473, hlam, p10469_0]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                rcases p10469_3 (m.d 0 2) (by simp) with h10480 | h10480
                                                · rcases p10469_3 (m.d 1 2) (by simp) with h10481 | h10481
                                                  · rcases p10469_3 (m.d 2 3) (by simp) with h10482 | h10482
                                                    · linarith only [h10060, h10482, hlam]
                                                    · linarith only [h10156, h10482, hlam]
                                                  · linarith only [h10151, h10481, hlam]
                                                · linarith only [h10480, hlam, p10469_0]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h0, h10058, h10059, h10150, h10155, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10161_1, p10469_1]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [hlam, p10469_0]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                rcases p10469_3 (m.d 0 2) (by simp) with h10489 | h10489
                                                · linarith only [h0, h10489, hlam]
                                                · linarith only [h10060, h10489, hlam]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h0, h10058, h10059, h10150, hlam, p10161_1, p10469_2]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                rcases p10469_3 (m.d 0 2) (by simp) with h10493 | h10493
                                                · linarith only [h0, h10493, hlam]
                                                · linarith only [h10062, h10493, hlam]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h10060, hlam, p10469_0]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h10149, hlam, p10469_0]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [hlam, p10469_0]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h10060, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10469_1, u0elo1]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h10060, hc25, hlam, hphi, ht0b, ht5b, p10469_1, u0elo1]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h10061, hlam, p10469_0]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h10150, hlam, p10469_0]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h10155, hlam, p10469_1]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [hlam, p10469_0]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h10157, hlam, p10469_1]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h10062, hlam, p10469_0]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h10151, hlam, p10469_0]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h10156, hlam, p10469_1]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [h10062, h10155, hc34, hlam, hphi, ht0b, ht45, ht5b, p10469_1, u0elo1]
                                              · have p10469_0 := h10469c.1
                                                have p10469_1 := h10469c.2.1
                                                have p10469_2 := h10469c.2.2.1
                                                have p10469_3 := h10469c.2.2.2
                                                linarith only [hlam, p10469_0]
                                          · linarith only [h10065, h10340, hlam]
                                      · linarith only [h10063, h10337, hlam]
                                    · linarith only [h10061, h10336, hlam]
                                  · linarith only [h10058, h10335, hlam]
                                · have p10161_0 := h10161c.1
                                  have p10161_1 := h10161c.2.1
                                  have p10161_2 := h10161c.2.2.1
                                  have p10161_3 := h10161c.2.2.2
                                  linarith only [hlam, p10161_0]
                          · linarith only [h10060, h10064, h10155, h10156, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10517 | h10517
                          · linarith only [h10060, h10063, h10155, h10517, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10519 | h10519
                            · linarith only [h10058, h10065, h10152, h10155, h10519, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10521 | h10521
                              · linarith only [h10058, h10065, h10152, h10521, hlam]
                              · rcases h0bigk with h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [hlam, p10523_0]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h0, hlam, p10523_1]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h6793, hlam, p10523_0]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10058, h10149, h10152, h10155, h6793, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10523_1]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10058, h10065, h10149, h10152, h10155, h6793, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10523_1]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10058, h10152, h10155, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10523_1, u0elo1]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [hlam, p10523_0]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10058, h10152, h10155, h6793, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10523_1, u0elo1]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10058, h10152, h10155, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10523_1, u0elo1]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10058, h10065, h10152, h10155, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10523_1, u0elo1]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10058, h10152, h10155, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10523_1, u0elo2]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10060, hlam, p10523_1]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [hlam, p10523_0]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10058, h10060, h10152, h10155, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10523_1, u0elo1]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10058, h10060, h10065, h10152, h10155, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10523_1, u0elo1]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10058, hlam, p10523_0]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10061, hlam, p10523_0]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10063, hlam, p10523_0]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [hlam, p10523_0]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10065, hlam, p10523_0]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10059, hlam, p10523_0]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10062, hlam, p10523_1]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10064, hlam, p10523_0]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [h10058, h10152, h10155, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10523_1, u0elo4]
                                · have p10523_0 := h10523c.1
                                  have p10523_1 := h10523c.2.1
                                  have p10523_2 := h10523c.2.2.1
                                  have p10523_3 := h10523c.2.2.2
                                  linarith only [hlam, p10523_0]
                    · linarith only [h10063, h10152, h6793, hlam]
                  · linarith only [h0, h10062, h10151, hlam]
                · linarith only [h0, h10061, h10150, hlam]
              · linarith only [h0, h10060, h10149, hlam]
          · linarith only [h10059, h10064, h6793, hlam]
        · linarith only [h10058, h10063, h6793, hlam]
      · linarith only [h10059, h10060, h10062, h6793, hlam]
    · linarith only [h10058, h10060, h10061, h6793, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h10557 | h10557
    · rcases m.htr 0 2 5 (by decide) (by decide) with h10558 | h10558
      · rcases m.htr 0 3 4 (by decide) (by decide) with h10559 | h10559
        · rcases m.htr 0 3 5 (by decide) (by decide) with h10560 | h10560
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10561 | h10561
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10562 | h10562
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10563 | h10563
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10564 | h10564
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10565 | h10565
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10566 | h10566
                      · linarith only [h0, h10058, h10060, h10562, h10566, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h10058, h10060, h10561, h10562, h10566, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h10060, h10559, h10562, h10565, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h10058, h10060, h10562, h10563, h10564, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h10058, h10060, h10562, h10563, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10572 | h10572
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10573 | h10573
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10574 | h10574
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10575 | h10575
                      · linarith only [h0, h10058, h10562, h10575, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h10058, h10561, h10562, h10574, h10575, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h10559, h10574, h6793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h10558, h10573, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h10557, h10572, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10581 | h10581
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10582 | h10582
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10583 | h10583
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10584 | h10584
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10585 | h10585
                      · linarith only [h10058, h10561, h10585, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10587 | h10587
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10588 | h10588
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10589 | h10589
                            · linarith only [h10058, h10561, h10582, h10589, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10591 | h10591
                              · linarith only [h10058, h10561, h10582, h10587, h10591, hlam]
                              · rcases h0bigk with h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c | h10593c
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [hlam, p10593_0]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h0, hlam, p10593_1]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h6793, hlam, p10593_0]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h0, h10058, h10060, h10581, h10582, h10587, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10593_1]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h0, h10060, h10581, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10593_1]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h10060, h10581, hc01, hc12, hlam, hphi, p10593_1]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [hlam, p10593_0]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h10060, hlam, p10593_0]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h10058, h10060, h10581, h10582, h10587, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10593_1]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h10059, h10060, h10581, h10582, h10585, h10587, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10593_1]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h10059, h10582, h10585, h10587, hc34, hlam, hphi, ht0b, ht45, ht5b, p10593_1, u0elo2]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h0, h10059, h10060, h10581, h10582, h10585, h10587, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10593_1]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [hlam, p10593_0]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  rcases p10593_3 (m.d 0 1) (by simp) with h10607 | h10607
                                  · linarith only [h10607, h6793, hlam]
                                  · linarith only [h10058, h10607, hlam]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  rcases p10593_3 (m.d 0 1) (by simp) with h10610 | h10610
                                  · linarith only [h10610, h6793, hlam]
                                  · linarith only [h10059, h10610, hlam]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h10058, hlam, p10593_0]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h10557, hlam, p10593_0]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h10559, hlam, p10593_0]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [hlam, p10593_0]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h10561, hlam, p10593_0]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h10059, hlam, p10593_0]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h10558, hlam, p10593_1]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h10560, hlam, p10593_0]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [h0, h10058, h10059, h10060, h10581, h10582, h10587, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10593_1]
                                · have p10593_0 := h10593c.1
                                  have p10593_1 := h10593c.2.1
                                  have p10593_2 := h10593c.2.2.1
                                  have p10593_3 := h10593c.2.2.2
                                  linarith only [hlam, p10593_0]
                          · linarith only [h10060, h10560, h10588, hlam]
                        · linarith only [h10060, h10559, h10587, hlam]
                    · linarith only [h0, h10059, h10060, h10559, h10581, h10584, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h0, h10058, h10060, h10581, h10582, h10583, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h10060, h10581, h10582, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10628 | h10628
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10629 | h10629
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10630 | h10630
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10631 | h10631
                      · linarith only [h10058, h10561, h10631, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10633 | h10633
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10634 | h10634
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10635 | h10635
                            · linarith only [h10058, h10561, h10628, h10635, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10637 | h10637
                              · linarith only [h10058, h10561, h10628, h10633, h10637, hlam]
                              · rcases h0bigk with h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [hlam, p10639_0]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h0, hlam, p10639_1]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h6793, hlam, p10639_0]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h0, h10581, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10639_1]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h0, h10581, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10639_1]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h10059, hc15, hlam, hphi, ht0b, ht5b, p10639_1, u0elo1]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [hlam, p10639_0]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h10060, hlam, p10639_0]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  rcases p10639_3 (m.d 0 1) (by simp) with h10648 | h10648
                                  · linarith only [h0, h10648, hlam]
                                  · linarith only [h10058, h10648, hlam]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  rcases p10639_3 (m.d 0 1) (by simp) with h10651 | h10651
                                  · linarith only [h0, h10651, hlam]
                                  · linarith only [h10059, h10651, hlam]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h10059, h10628, h10631, h10633, hc34, hlam, hphi, ht0b, ht45, ht5b, p10639_1, u0elo2]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h0, h10059, h10628, h10631, h10633, hc34, hlam, hphi, ht0b, ht45, ht5b, p10639_1, u0elo2]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [hlam, p10639_0]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  rcases p10639_3 (m.d 0 1) (by simp) with h10657 | h10657
                                  · linarith only [h10657, h6793, hlam]
                                  · linarith only [h10058, h10657, hlam]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  rcases p10639_3 (m.d 0 1) (by simp) with h10660 | h10660
                                  · linarith only [h10660, h6793, hlam]
                                  · linarith only [h10059, h10660, hlam]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h10058, hlam, p10639_0]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h10557, hlam, p10639_0]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h10559, hlam, p10639_0]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [hlam, p10639_0]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h10561, hlam, p10639_0]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h10059, hlam, p10639_0]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h10558, hlam, p10639_1]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h10560, hlam, p10639_0]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [h0, h10058, h10059, h10581, h10628, h10633, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10639_1]
                                · have p10639_0 := h10639c.1
                                  have p10639_1 := h10639c.2.1
                                  have p10639_2 := h10639c.2.2.1
                                  have p10639_3 := h10639c.2.2.2
                                  linarith only [hlam, p10639_0]
                          · linarith only [h0, h10581, h10634, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h10581, h10633, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h10059, h10559, h10561, h10630, h6793, hlam]
                  · linarith only [h0, h10558, h10629, hlam]
                · linarith only [h0, h10557, h10628, hlam]
          · linarith only [h0, h10059, h10060, h10560, hlam]
        · linarith only [h0, h10058, h10060, h10559, hlam]
      · linarith only [h0, h10059, h10558, hlam]
    · linarith only [h0, h10058, h10557, hlam]

end R2N4
