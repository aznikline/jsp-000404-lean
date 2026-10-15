import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_44S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5626000 in
set_option maxHeartbeats 5626000 in
theorem r1l7_21_15_M_IR_L_I_s3_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h2004 | h2004
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2005 | h2005
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2006 | h2006
      · linarith only [h0, h2006, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2008 | h2008
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2009 | h2009
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2010 | h2010
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2011 | h2011
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2012 | h2012
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2013 | h2013
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2014 | h2014
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2015 | h2015
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2016 | h2016
                        · rcases h1bigk with h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h2008, h2013, h2016, hc01, hc45, hlam, hphi, ht0b, ht5b, p2017_1]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h2006, h2008, h2013, h2016, hc01, hc45, hlam, hphi, ht0b, ht5b, p2017_1]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            rcases p2017_3 (m.d 0 1) (by simp) with h2021 | h2021
                            · rcases p2017_3 (m.d 1 2) (by simp) with h2022 | h2022
                              · linarith only [h0, h2022, hlam]
                              · linarith only [h2008, h2022, hlam]
                            · linarith only [h2021, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            rcases p2017_3 (m.d 0 1) (by simp) with h2026 | h2026
                            · rcases p2017_3 (m.d 1 2) (by simp) with h2027 | h2027
                              · linarith only [h0, h2027, hlam]
                              · linarith only [h2009, h2027, hlam]
                            · linarith only [h2026, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h0, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h2006, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h2012, hc12, hlam, hphi, p2017_1, u1ehi4]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h0, h4, hc23, hlam, hphi, ht12, p2017_1, u1ehi4]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2017_1, u1ehi1]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1, h2012, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2017_1, u1ehi4]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2017_1, u1ehi4]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h2, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h2008, hlam, p2017_1]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h2010, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [hc14, hlam, hphi, p2017_1, u1ehi4]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h3, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h2009, hlam, p2017_1]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h2011, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h2012, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [hlam, p2017_0]
                        · linarith only [h0, h2008, h2015, h2016, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2052 | h2052
                        · linarith only [h2013, h2015, h2052, hlam]
                        · rcases h1bigk with h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [hlam, p2054_0]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h2008, h2012, h2013, h2015, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2054_1]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h2006, h2008, h2012, h2013, h2015, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2054_1]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h2012, h2013, h2015, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2054_1]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            rcases p2054_3 (m.d 0 1) (by simp) with h2059 | h2059
                            · rcases p2054_3 (m.d 1 2) (by simp) with h2060 | h2060
                              · linarith only [h0, h2060, hlam]
                              · linarith only [h2009, h2060, hlam]
                            · linarith only [h2059, hlam, p2054_0]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h0, hlam, p2054_0]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [hlam, p2054_0]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h2006, hlam, p2054_0]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h2012, h2013, h2015, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2054_1]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h0, h4, hc23, hlam, hphi, ht12, p2054_1, u1ehi4]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h1, hlam, p2054_0]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2054_1, u1ehi1]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [hlam, p2054_0]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h1, h2012, h2013, h2015, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2054_1]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h0, h1, h2008, h2012, h2013, h2015, h4, hc01, hc23, hc34, hlam, hphi, ht0b, ht12, ht45, ht5b, p2054_1, u1ehi4]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h2, hlam, p2054_0]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h2008, hlam, p2054_1]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h2010, hlam, p2054_0]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [hlam, p2054_0]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h0, h2008, h4, hc23, hlam, hphi, ht12, p2054_1, u1ehi4]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h3, hlam, p2054_0]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h2009, hlam, p2054_1]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h2011, hlam, p2054_0]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [h2012, hlam, p2054_0]
                          · have p2054_0 := h2054c.1
                            have p2054_1 := h2054c.2.1
                            have p2054_2 := h2054c.2.2.1
                            have p2054_3 := h2054c.2.2.2
                            linarith only [hlam, p2054_0]
                    · linarith only [h0, h2014, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h0, h2008, h2012, h2013, h4, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2086 | h2086
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2087 | h2087
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2088 | h2088
                      · linarith only [h2012, h2088, hc24, hlam, hphi, ht12, u1ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2090 | h2090
                        · linarith only [h0, h2009, h2012, h2086, h2088, h2090, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                        · rcases h1bigk with h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            rcases p2092_3 (m.d 0 1) (by simp) with h2094 | h2094
                            · rcases p2092_3 (m.d 1 2) (by simp) with h2095 | h2095
                              · linarith only [h2095, hlam, p2092_0]
                              · rcases p2092_3 (m.d 1 3) (by simp) with h2097 | h2097
                                · linarith only [h1, h2097, hlam]
                                · linarith only [h2006, h2097, hlam]
                            · linarith only [h2094, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            rcases p2092_3 (m.d 0 1) (by simp) with h2101 | h2101
                            · rcases p2092_3 (m.d 1 2) (by simp) with h2102 | h2102
                              · linarith only [h0, h2102, hlam]
                              · rcases p2092_3 (m.d 1 3) (by simp) with h2104 | h2104
                                · linarith only [h2104, hlam, p2092_0]
                                · rcases p2092_3 (m.d 1 4) (by simp) with h2106 | h2106
                                  · linarith only [h2, h2106, hlam]
                                  · rcases p2092_3 (m.d 1 5) (by simp) with h2108 | h2108
                                    · linarith only [h2108, h3, hlam]
                                    · rcases h5bigk with h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [hlam, p2110_0]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2004, h2012, h4, hc23, hlam, hphi, ht12, p2110_1, u1ehi3]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        rcases p2110_3 (m.d 0 5) (by simp) with h2113 | h2113
                                        · rcases p2110_3 (m.d 1 5) (by simp) with h2114 | h2114
                                          · linarith only [h2114, h3, hlam]
                                          · linarith only [h2009, h2114, hlam]
                                        · linarith only [h2113, hlam, p2110_0]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        rcases p2110_3 (m.d 0 5) (by simp) with h2118 | h2118
                                        · rcases p2110_3 (m.d 1 5) (by simp) with h2119 | h2119
                                          · linarith only [h2119, h3, hlam]
                                          · linarith only [h2011, h2119, hlam]
                                        · linarith only [h2004, h2118, hlam]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2004, h2012, h4, hc23, hlam, hphi, ht12, p2110_1, u1ehi3]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h3, hlam, p2110_0]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [hlam, p2110_0]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2006, h2009, h2088, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2092_1, p2110_1]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2006, h2009, hc01, hc35, hlam, hphi, ht0b, ht5b, p2092_1, p2110_1]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2012, hlam, p2110_1]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h3, hc25, hlam, hphi, ht12, p2110_1, u1ehi4]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2009, hlam, p2110_1]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [hlam, p2110_0]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2006, h2009, h2090, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2092_1, p2110_1]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2088, hlam, p2110_1]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2004, hlam, p2110_0]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2011, hlam, p2110_0]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2087, hlam, p2110_0]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [hlam, p2110_0]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2090, hlam, p2110_1]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2005, hlam, p2110_0]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [h2005, h2012, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2110_1, u1ehi3]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        rcases p2110_3 (m.d 0 5) (by simp) with h2141 | h2141
                                        · rcases p2110_3 (m.d 1 5) (by simp) with h2142 | h2142
                                          · linarith only [h2012, h2142, hlam]
                                          · linarith only [h2009, h2142, hlam]
                                        · linarith only [h2006, h2009, h2012, h2141, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2092_1, u1ehi3]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        rcases p2110_3 (m.d 0 5) (by simp) with h2146 | h2146
                                        · rcases p2110_3 (m.d 1 5) (by simp) with h2147 | h2147
                                          · linarith only [h2012, h2147, hlam]
                                          · linarith only [h2011, h2147, hlam]
                                        · linarith only [h2004, h2146, hlam]
                                      · have p2110_0 := h2110c.1
                                        have p2110_1 := h2110c.2.1
                                        have p2110_2 := h2110c.2.2.1
                                        have p2110_3 := h2110c.2.2.2
                                        linarith only [hlam, p2110_0]
                            · linarith only [h2101, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            rcases p2092_3 (m.d 0 1) (by simp) with h2153 | h2153
                            · rcases p2092_3 (m.d 1 2) (by simp) with h2154 | h2154
                              · linarith only [h0, h2154, hlam]
                              · linarith only [h2008, h2154, hlam]
                            · linarith only [h2153, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            rcases p2092_3 (m.d 0 1) (by simp) with h2158 | h2158
                            · rcases p2092_3 (m.d 1 2) (by simp) with h2159 | h2159
                              · linarith only [h0, h2159, hlam]
                              · linarith only [h2009, h2159, hlam]
                            · linarith only [h2158, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h0, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h2006, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [hc12, hlam, hphi, p2092_1, u1ehi3]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h0, h2012, h4, hc23, hlam, hphi, ht12, p2092_1, u1ehi3]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h1, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h1, h2009, hc01, hc25, hlam, hphi, ht0b, ht5b, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2092_1, u1ehi3]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h1, h2012, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2092_1, u1ehi3]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h2, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h2008, hlam, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h2010, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h2012, hlam, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h3, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h2009, hlam, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h2011, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h2009, hc12, hlam, hphi, p2092_1, u1ehi3]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [hlam, p2092_0]
                    · linarith only [h0, h2087, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h2004, h2005, h2012, h2086, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
              · linarith only [h2004, h2011, h4, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h2006, h2008, h2010, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2187 | h2187
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2188 | h2188
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2189 | h2189
                · linarith only [h2008, h2009, h2189, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2191 | h2191
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2192 | h2192
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2193 | h2193
                      · linarith only [h2189, h2193, hc24, hlam, hphi, ht12, u1ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2195 | h2195
                        · linarith only [h2008, h2009, h2189, h2191, h2195, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases h1bigk with h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c | h2197c
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            rcases p2197_3 (m.d 0 1) (by simp) with h2199 | h2199
                            · rcases p2197_3 (m.d 1 2) (by simp) with h2200 | h2200
                              · linarith only [h2200, hlam, p2197_0]
                              · rcases p2197_3 (m.d 1 3) (by simp) with h2202 | h2202
                                · linarith only [h1, h2202, hlam]
                                · linarith only [h2006, h2202, hlam]
                            · linarith only [h2199, hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            rcases p2197_3 (m.d 0 1) (by simp) with h2206 | h2206
                            · rcases p2197_3 (m.d 1 2) (by simp) with h2207 | h2207
                              · linarith only [h0, h2207, hlam]
                              · rcases p2197_3 (m.d 1 3) (by simp) with h2209 | h2209
                                · linarith only [h2209, hlam, p2197_0]
                                · rcases p2197_3 (m.d 1 4) (by simp) with h2211 | h2211
                                  · linarith only [h2, h2211, hlam]
                                  · rcases p2197_3 (m.d 1 5) (by simp) with h2213 | h2213
                                    · linarith only [h2213, h3, hlam]
                                    · rcases h5bigk with h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [hlam, p2215_0]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2004, h4, hc23, hlam, hphi, ht12, p2215_1, u1ehi4]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2004, h2009, h4, hc12, hc23, hlam, hphi, p2215_1]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        rcases p2215_3 (m.d 0 5) (by simp) with h2219 | h2219
                                        · rcases p2215_3 (m.d 1 5) (by simp) with h2220 | h2220
                                          · linarith only [h2220, h3, hlam]
                                          · linarith only [h2188, h2220, hlam]
                                        · linarith only [h2004, h2219, hlam]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2004, h2189, h4, hc23, hlam, hphi, ht12, p2215_1, u1ehi3]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h3, hlam, p2215_0]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [hlam, p2215_0]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2009, hlam, p2215_0]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2188, hc01, hc35, hlam, hphi, ht0b, ht5b, p2197_1, p2215_1]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2189, hlam, p2215_1]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h3, hc25, hlam, hphi, ht12, p2215_1, u1ehi4]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [hc25, hlam, hphi, ht12, p2215_1, u1ehi4]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [hlam, p2215_0]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        rcases p2215_3 (m.d 0 5) (by simp) with h2233 | h2233
                                        · rcases p2215_3 (m.d 1 5) (by simp) with h2234 | h2234
                                          · linarith only [h2009, h2234, hlam]
                                          · linarith only [h2188, h2234, hlam]
                                        · linarith only [h2004, h2233, hlam]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2193, hlam, p2215_1]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2004, hlam, p2215_0]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2188, hlam, p2215_0]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2192, hlam, p2215_0]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [hlam, p2215_0]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2195, hlam, p2215_1]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2005, hlam, p2215_0]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2, h2005, h2008, h2009, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2215_1, u1ehi3]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [h2, h2005, h2008, h2009, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2215_1, u1ehi3]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        rcases p2215_3 (m.d 0 5) (by simp) with h2247 | h2247
                                        · rcases p2215_3 (m.d 1 5) (by simp) with h2248 | h2248
                                          · linarith only [h2189, h2248, hlam]
                                          · linarith only [h2188, h2248, hlam]
                                        · linarith only [h2004, h2247, hlam]
                                      · have p2215_0 := h2215c.1
                                        have p2215_1 := h2215c.2.1
                                        have p2215_2 := h2215c.2.2.1
                                        have p2215_3 := h2215c.2.2.2
                                        linarith only [hlam, p2215_0]
                            · linarith only [h2206, hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            rcases p2197_3 (m.d 0 1) (by simp) with h2254 | h2254
                            · rcases p2197_3 (m.d 1 2) (by simp) with h2255 | h2255
                              · linarith only [h0, h2255, hlam]
                              · linarith only [h2008, h2255, hlam]
                            · linarith only [h2254, hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            rcases p2197_3 (m.d 0 1) (by simp) with h2259 | h2259
                            · rcases p2197_3 (m.d 1 2) (by simp) with h2260 | h2260
                              · linarith only [h0, h2260, hlam]
                              · rcases p2197_3 (m.d 1 3) (by simp) with h2262 | h2262
                                · linarith only [h1, h2262, hlam]
                                · linarith only [h2188, h2262, hlam]
                            · linarith only [h2259, hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h0, hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h2006, hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [hc12, hlam, hphi, p2197_1, u1ehi3]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h2009, hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h1, hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [hc13, hlam, hphi, p2197_1, u1ehi1]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2197_1, u1ehi3]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2197_1, u1ehi4]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h2, hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h2008, hlam, p2197_1]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h2187, hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h2189, hlam, p2197_1]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h3, hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h2008, hc15, hlam, hphi, p2197_1, u1ehi3]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h2188, hlam, p2197_0]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [h2, h2005, h2189, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2197_1, u1ehi3]
                          · have p2197_0 := h2197c.1
                            have p2197_1 := h2197c.2.1
                            have p2197_2 := h2197c.2.2.1
                            have p2197_3 := h2197c.2.2.2
                            linarith only [hlam, p2197_0]
                    · linarith only [h0, h2008, h2192, h4, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                  · linarith only [h2004, h2005, h2189, h2191, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
              · linarith only [h2004, h2188, h4, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h2006, h2008, h2187, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2290 | h2290
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2291 | h2291
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2292 | h2292
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2293 | h2293
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2294 | h2294
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2295 | h2295
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2296 | h2296
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2297 | h2297
                        · rcases h1bigk with h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            rcases p2298_3 (m.d 0 1) (by simp) with h2300 | h2300
                            · rcases p2298_3 (m.d 1 2) (by simp) with h2301 | h2301
                              · linarith only [h2301, hlam, p2298_0]
                              · rcases p2298_3 (m.d 1 3) (by simp) with h2303 | h2303
                                · linarith only [h1, h2303, hlam]
                                · linarith only [h2006, h2303, hlam]
                            · linarith only [h2300, hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h2291, h2297, hc01, hc45, hlam, hphi, ht0b, ht5b, p2298_1]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            rcases p2298_3 (m.d 0 1) (by simp) with h2308 | h2308
                            · rcases p2298_3 (m.d 1 2) (by simp) with h2309 | h2309
                              · linarith only [h0, h2309, hlam]
                              · rcases p2298_3 (m.d 1 3) (by simp) with h2311 | h2311
                                · linarith only [h1, h2311, hlam]
                                · linarith only [h2291, h2311, hlam]
                            · linarith only [h2308, hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            rcases p2298_3 (m.d 0 1) (by simp) with h2315 | h2315
                            · rcases p2298_3 (m.d 1 2) (by simp) with h2316 | h2316
                              · linarith only [h0, h2316, hlam]
                              · linarith only [h2290, h2316, hlam]
                            · linarith only [h2315, hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h0, hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h2006, hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h2008, hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [hc12, hlam, hphi, p2298_1, u1ehi4]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h1, hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [hc13, hlam, hphi, p2298_1, u1ehi1]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2298_1, u1ehi3]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2298_1, u1ehi4]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h2, hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h2290, hc14, hlam, hphi, p2298_1, u1ehi4]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h2291, hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h1, h2291, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2298_1, u1ehi4]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h3, hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h2290, hlam, p2298_1]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h2292, hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [h2293, hlam, p2298_0]
                          · have p2298_0 := h2298c.1
                            have p2298_1 := h2298c.2.1
                            have p2298_2 := h2298c.2.2.1
                            have p2298_3 := h2298c.2.2.2
                            linarith only [hlam, p2298_0]
                        · rcases h1bigk with h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h2290, h2296, h2297, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2340_1]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h2006, h2290, h2296, h2297, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2340_1]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h2008, h2290, h2296, h2297, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2340_1]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            rcases p2340_3 (m.d 0 1) (by simp) with h2345 | h2345
                            · rcases p2340_3 (m.d 1 2) (by simp) with h2346 | h2346
                              · linarith only [h0, h2346, hlam]
                              · linarith only [h2290, h2346, hlam]
                            · linarith only [h2345, hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h0, hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h2006, hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h2008, hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h0, h4, hc23, hlam, hphi, ht12, p2340_1, u1ehi4]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h1, hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h2290, h2296, h2297, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2340_1]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h1, h2008, h2290, h2296, h2297, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2340_1]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h0, h1, h2290, h2296, h2297, h4, hc01, hc23, hc34, hlam, hphi, ht0b, ht12, ht45, ht5b, p2340_1, u1ehi4]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h2, hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h2290, h2296, h2297, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2340_1]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h2291, hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h0, h1, h2290, h2291, h2296, h2297, h4, hc01, hc23, hc34, hlam, hphi, ht0b, ht12, ht45, ht5b, p2340_1, u1ehi4]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h3, hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h2290, hlam, p2340_1]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h2292, hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [h2293, hlam, p2340_0]
                          · have p2340_0 := h2340c.1
                            have p2340_1 := h2340c.2.1
                            have p2340_2 := h2340c.2.2.1
                            have p2340_3 := h2340c.2.2.2
                            linarith only [hlam, p2340_0]
                      · linarith only [h2, h2005, h2008, h2290, h2296, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h2295, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h0, h2290, h2294, h4, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                · linarith only [h2008, h2290, h2293, hlam]
              · linarith only [h2004, h2292, h4, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2375 | h2375
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2376 | h2376
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2377 | h2377
                  · linarith only [h2006, h2290, h2291, h2377, hc23, hlam, hphi, ht12, u1ehi4]
                  · linarith only [h0, h2290, h2377, h4, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                · linarith only [h2006, h2290, h2291, h2376, hlam]
              · linarith only [h2004, h2006, h2290, h2375, h4, hc23, hlam, hphi, ht12, u1ehi4]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2382 | h2382
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2383 | h2383
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2384 | h2384
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2385 | h2385
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2386 | h2386
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2387 | h2387
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2388 | h2388
                        · rcases h1bigk with h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            rcases p2389_3 (m.d 0 1) (by simp) with h2391 | h2391
                            · rcases p2389_3 (m.d 1 2) (by simp) with h2392 | h2392
                              · linarith only [h2392, hlam, p2389_0]
                              · rcases p2389_3 (m.d 1 3) (by simp) with h2394 | h2394
                                · linarith only [h1, h2394, hlam]
                                · linarith only [h2006, h2394, hlam]
                            · linarith only [h2391, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2382, h2388, hc01, hc45, hlam, hphi, ht0b, ht5b, p2389_1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            rcases p2389_3 (m.d 0 1) (by simp) with h2399 | h2399
                            · rcases p2389_3 (m.d 1 2) (by simp) with h2400 | h2400
                              · linarith only [h0, h2400, hlam]
                              · rcases p2389_3 (m.d 1 3) (by simp) with h2402 | h2402
                                · linarith only [h1, h2402, hlam]
                                · linarith only [h2382, h2402, hlam]
                            · linarith only [h2399, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            rcases p2389_3 (m.d 0 1) (by simp) with h2406 | h2406
                            · rcases p2389_3 (m.d 1 2) (by simp) with h2407 | h2407
                              · linarith only [h0, h2407, hlam]
                              · rcases p2389_3 (m.d 1 3) (by simp) with h2409 | h2409
                                · linarith only [h1, h2409, hlam]
                                · linarith only [h2383, h2409, hlam]
                            · linarith only [h2406, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h0, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2006, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2008, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2290, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h1, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [hc13, hlam, hphi, p2389_1, u1ehi1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h1, h2290, h2384, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2389_1, u1ehi1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h1, h2290, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2389_1, u1ehi1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [hc14, hlam, hphi, p2389_1, u1ehi1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2382, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h1, h2290, h2382, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2389_1, u1ehi1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h3, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [hc15, hlam, hphi, p2389_1, u1ehi1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2383, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2384, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [hlam, p2389_0]
                        · rcases h1bigk with h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            rcases p2433_3 (m.d 0 1) (by simp) with h2435 | h2435
                            · rcases p2433_3 (m.d 1 2) (by simp) with h2436 | h2436
                              · linarith only [h2436, hlam, p2433_0]
                              · rcases p2433_3 (m.d 1 3) (by simp) with h2438 | h2438
                                · linarith only [h1, h2438, hlam]
                                · linarith only [h2006, h2438, hlam]
                            · linarith only [h2435, hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h2382, h2384, h2388, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2433_1]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h2384, h2388, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2433_1]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            rcases p2433_3 (m.d 0 1) (by simp) with h2444 | h2444
                            · rcases p2433_3 (m.d 1 2) (by simp) with h2445 | h2445
                              · linarith only [h0, h2445, hlam]
                              · rcases p2433_3 (m.d 1 3) (by simp) with h2447 | h2447
                                · linarith only [h1, h2447, hlam]
                                · linarith only [h2383, h2447, hlam]
                            · linarith only [h2444, hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h0, hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h2006, hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h2008, hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h2290, hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h1, hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [hc13, hlam, hphi, p2433_1, u1ehi1]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h1, h2384, h2388, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2433_1]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2433_1, u1ehi4]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h2, hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [hc14, hlam, hphi, p2433_1, u1ehi1]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h2382, hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h1, h2290, h2382, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2433_1, u1ehi1]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h3, hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [hc15, hlam, hphi, p2433_1, u1ehi1]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h2383, hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [h2384, hlam, p2433_0]
                          · have p2433_0 := h2433c.1
                            have p2433_1 := h2433c.2.1
                            have p2433_2 := h2433c.2.2.1
                            have p2433_3 := h2433c.2.2.2
                            linarith only [hlam, p2433_0]
                      · linarith only [h2, h2005, h2008, h2387, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                    · linarith only [h0, h2386, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h0, h2385, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2474 | h2474
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2475 | h2475
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2476 | h2476
                      · linarith only [h2384, h2476, hc24, hlam, hphi, ht12, u1ehi3]
                      · linarith only [h2004, h2005, h2008, h2476, h4, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h1, h2383, h2475, h4, hlam]
                  · linarith only [h1, h2382, h2384, h2474, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · linarith only [h2004, h2383, h4, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2482 | h2482
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2483 | h2483
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2484 | h2484
                  · linarith only [h2290, h2382, h2482, h2484, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h0, h2484, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h2382, h2482, h2483, hlam]
              · linarith only [h2004, h2482, h4, hc23, hlam, hphi, ht12, u1ehi2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2489 | h2489
      · linarith only [h0, h2489, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2491 | h2491
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2492 | h2492
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2493 | h2493
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2494 | h2494
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2495 | h2495
                · linarith only [h2, h2005, h2495, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2497 | h2497
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2498 | h2498
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2499 | h2499
                      · linarith only [h0, h2005, h2491, h2499, h3, h4, hc23, hlam, hphi, ht12, u1ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2501 | h2501
                        · linarith only [h0, h2, h2005, h2492, h2497, h2499, h2501, h4, hc23, hlam, hphi, ht12, u1ehi3]
                        · rcases h1bigk with h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            rcases p2503_3 (m.d 0 1) (by simp) with h2505 | h2505
                            · rcases p2503_3 (m.d 1 2) (by simp) with h2506 | h2506
                              · linarith only [h2506, hlam, p2503_0]
                              · rcases p2503_3 (m.d 1 3) (by simp) with h2508 | h2508
                                · linarith only [h1, h2508, hlam]
                                · linarith only [h2489, h2508, hlam]
                            · linarith only [h2505, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            rcases p2503_3 (m.d 0 1) (by simp) with h2512 | h2512
                            · rcases p2503_3 (m.d 1 2) (by simp) with h2513 | h2513
                              · linarith only [h0, h2513, hlam]
                              · rcases p2503_3 (m.d 1 3) (by simp) with h2515 | h2515
                                · linarith only [h2515, hlam, p2503_0]
                                · rcases p2503_3 (m.d 1 4) (by simp) with h2517 | h2517
                                  · linarith only [h2, h2517, hlam]
                                  · rcases p2503_3 (m.d 1 5) (by simp) with h2519 | h2519
                                    · linarith only [h2519, h3, hlam]
                                    · rcases h5bigk with h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [hlam, p2521_0]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2004, h2495, h4, hc23, hlam, hphi, ht12, p2521_1, u1ehi3]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        rcases p2521_3 (m.d 0 5) (by simp) with h2524 | h2524
                                        · rcases p2521_3 (m.d 1 5) (by simp) with h2525 | h2525
                                          · linarith only [h2525, h3, hlam]
                                          · linarith only [h2492, h2525, hlam]
                                        · linarith only [h2524, hlam, p2521_0]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        rcases p2521_3 (m.d 0 5) (by simp) with h2529 | h2529
                                        · rcases p2521_3 (m.d 1 5) (by simp) with h2530 | h2530
                                          · linarith only [h2530, h3, hlam]
                                          · linarith only [h2494, h2530, hlam]
                                        · linarith only [h2004, h2529, hlam]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2005, hlam, p2521_1]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h3, hlam, p2521_0]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [hlam, p2521_0]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2489, h2492, h2499, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2503_1, p2521_1]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2489, h2492, hc01, hc35, hlam, hphi, ht0b, ht5b, p2503_1, p2521_1]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2495, hlam, p2521_1]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h3, hc25, hlam, hphi, ht12, p2521_1, u1ehi4]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2492, hlam, p2521_1]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [hlam, p2521_0]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2489, h2492, h2501, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2503_1, p2521_1]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2499, hlam, p2521_1]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2004, hlam, p2521_0]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2494, hlam, p2521_0]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2498, hlam, p2521_0]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [hlam, p2521_0]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2501, hlam, p2521_1]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2, h2005, hc45, hlam, hphi, ht12, ht23, ht34, p2521_1, u1ehi3]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [h2495, hc45, hlam, hphi, ht12, ht23, ht34, p2521_1, u1ehi3]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        rcases p2521_3 (m.d 0 5) (by simp) with h2552 | h2552
                                        · linarith only [h2005, h2552, hlam]
                                        · linarith only [h2, h2005, h2489, h2492, h2552, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2503_1, u1ehi3]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        rcases p2521_3 (m.d 0 5) (by simp) with h2555 | h2555
                                        · linarith only [h2005, h2555, hlam]
                                        · linarith only [h2004, h2555, hlam]
                                      · have p2521_0 := h2521c.1
                                        have p2521_1 := h2521c.2.1
                                        have p2521_2 := h2521c.2.2.1
                                        have p2521_3 := h2521c.2.2.2
                                        linarith only [hlam, p2521_0]
                            · linarith only [h2512, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            rcases p2503_3 (m.d 0 1) (by simp) with h2560 | h2560
                            · rcases p2503_3 (m.d 1 2) (by simp) with h2561 | h2561
                              · linarith only [h0, h2561, hlam]
                              · linarith only [h2491, h2561, hlam]
                            · linarith only [h2560, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            rcases p2503_3 (m.d 0 1) (by simp) with h2565 | h2565
                            · rcases p2503_3 (m.d 1 2) (by simp) with h2566 | h2566
                              · linarith only [h0, h2566, hlam]
                              · linarith only [h2492, h2566, hlam]
                            · linarith only [h2565, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h0, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h2489, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [hc12, hlam, hphi, p2503_1, u1ehi3]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h0, h2495, h4, hc23, hlam, hphi, ht12, p2503_1, u1ehi3]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h1, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h1, h2492, hc01, hc25, hlam, hphi, ht0b, ht5b, p2503_1]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2503_1, u1ehi3]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h1, h2495, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2503_1, u1ehi3]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h2, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h2491, hlam, p2503_1]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h2493, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h2495, hlam, p2503_1]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h3, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h2492, hlam, p2503_1]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h2494, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h2492, hc12, hlam, hphi, p2503_1, u1ehi3]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [hlam, p2503_0]
                    · linarith only [h0, h2498, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h0, h2492, h2495, h2497, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
              · linarith only [h2004, h2494, h4, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h2489, h2491, h2493, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2594 | h2594
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2595 | h2595
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2596 | h2596
                · linarith only [h2, h2005, h2596, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2598 | h2598
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2599 | h2599
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2600 | h2600
                      · linarith only [h2, h2005, h2491, h2492, h2600, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2602 | h2602
                        · linarith only [h2491, h2492, h2598, h2600, h2602, hlam]
                        · rcases h1bigk with h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            rcases p2604_3 (m.d 0 1) (by simp) with h2606 | h2606
                            · rcases p2604_3 (m.d 1 2) (by simp) with h2607 | h2607
                              · linarith only [h2607, hlam, p2604_0]
                              · rcases p2604_3 (m.d 1 3) (by simp) with h2609 | h2609
                                · linarith only [h1, h2609, hlam]
                                · linarith only [h2489, h2609, hlam]
                            · linarith only [h2606, hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            rcases p2604_3 (m.d 0 1) (by simp) with h2613 | h2613
                            · rcases p2604_3 (m.d 1 2) (by simp) with h2614 | h2614
                              · linarith only [h0, h2614, hlam]
                              · rcases p2604_3 (m.d 1 3) (by simp) with h2616 | h2616
                                · linarith only [h2616, hlam, p2604_0]
                                · rcases p2604_3 (m.d 1 4) (by simp) with h2618 | h2618
                                  · linarith only [h2, h2618, hlam]
                                  · rcases p2604_3 (m.d 1 5) (by simp) with h2620 | h2620
                                    · linarith only [h2620, h3, hlam]
                                    · rcases h5bigk with h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [hlam, p2622_0]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2004, h2492, h4, hc23, hlam, hphi, ht12, p2622_1, u1ehi1]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2491, h2492, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2622_1, u1ehi3]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        rcases p2622_3 (m.d 0 5) (by simp) with h2626 | h2626
                                        · rcases p2622_3 (m.d 1 5) (by simp) with h2627 | h2627
                                          · linarith only [h2627, h3, hlam]
                                          · linarith only [h2595, h2627, hlam]
                                        · linarith only [h2004, h2626, hlam]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2005, hlam, p2622_1]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h3, hlam, p2622_0]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [hlam, p2622_0]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2492, hlam, p2622_0]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2595, hc01, hc35, hlam, hphi, ht0b, ht5b, p2604_1, p2622_1]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2596, hlam, p2622_1]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h3, hc25, hlam, hphi, ht12, p2622_1, u1ehi4]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [hc25, hlam, hphi, ht12, p2622_1, u1ehi4]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [hlam, p2622_0]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        rcases p2622_3 (m.d 0 5) (by simp) with h2640 | h2640
                                        · rcases p2622_3 (m.d 1 5) (by simp) with h2641 | h2641
                                          · linarith only [h2492, h2641, hlam]
                                          · linarith only [h2595, h2641, hlam]
                                        · linarith only [h2004, h2640, hlam]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2600, hlam, p2622_1]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2004, hlam, p2622_0]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2595, hlam, p2622_0]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2599, hlam, p2622_0]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [hlam, p2622_0]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2602, hlam, p2622_1]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2491, h2492, h3, hc45, hlam, hphi, ht12, ht23, ht34, p2622_1, u1ehi3]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2491, h2492, hc45, hlam, hphi, ht12, ht23, ht34, p2622_1, u1ehi3]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [h2491, h2492, hc45, hlam, hphi, ht12, ht23, ht34, p2622_1, u1ehi3]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        rcases p2622_3 (m.d 0 5) (by simp) with h2654 | h2654
                                        · linarith only [h2005, h2654, hlam]
                                        · linarith only [h2004, h2654, hlam]
                                      · have p2622_0 := h2622c.1
                                        have p2622_1 := h2622c.2.1
                                        have p2622_2 := h2622c.2.2.1
                                        have p2622_3 := h2622c.2.2.2
                                        linarith only [hlam, p2622_0]
                            · linarith only [h2613, hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            rcases p2604_3 (m.d 0 1) (by simp) with h2659 | h2659
                            · rcases p2604_3 (m.d 1 2) (by simp) with h2660 | h2660
                              · linarith only [h0, h2660, hlam]
                              · linarith only [h2491, h2660, hlam]
                            · linarith only [h2659, hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            rcases p2604_3 (m.d 0 1) (by simp) with h2664 | h2664
                            · rcases p2604_3 (m.d 1 2) (by simp) with h2665 | h2665
                              · linarith only [h0, h2665, hlam]
                              · rcases p2604_3 (m.d 1 3) (by simp) with h2667 | h2667
                                · linarith only [h1, h2667, hlam]
                                · linarith only [h2595, h2667, hlam]
                            · linarith only [h2664, hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h0, hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h2489, hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [hc12, hlam, hphi, p2604_1, u1ehi3]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h2492, hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h1, hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [hc13, hlam, hphi, p2604_1, u1ehi1]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2604_1, u1ehi3]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2604_1, u1ehi4]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h2, hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h2491, hlam, p2604_1]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h2594, hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h2596, hlam, p2604_1]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h3, hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h2491, hc15, hlam, hphi, p2604_1, u1ehi3]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h2595, hlam, p2604_0]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [h1, h2595, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2604_1, u1ehi3]
                          · have p2604_0 := h2604c.1
                            have p2604_1 := h2604c.2.1
                            have p2604_2 := h2604c.2.2.1
                            have p2604_3 := h2604c.2.2.2
                            linarith only [hlam, p2604_0]
                    · linarith only [h0, h2491, h2599, h4, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                  · linarith only [h0, h2491, h2598, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
              · linarith only [h2004, h2595, h4, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h2489, h2491, h2594, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2695 | h2695
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2696 | h2696
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2697 | h2697
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2698 | h2698
                · linarith only [h2, h2005, h2698, hlam]
                · linarith only [h2491, h2695, h2698, hlam]
              · linarith only [h2004, h2491, h2696, h2697, h4, hc23, hlam, hphi, ht12, u1ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2702 | h2702
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2703 | h2703
                · linarith only [h2, h2005, h2703, hlam]
                · linarith only [h2489, h2695, h2696, h2703, hlam]
              · linarith only [h2004, h2489, h2702, h4, hc23, hlam, hphi, ht12, u1ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2707 | h2707
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2708 | h2708
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2709 | h2709
                · linarith only [h2, h2005, h2709, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2711 | h2711
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2712 | h2712
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2713 | h2713
                      · linarith only [h2, h2005, h2713, hc24, hlam, hphi, ht12, u1ehi3]
                      · linarith only [h2491, h2713, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h1, h2708, h2712, h4, hlam]
                  · linarith only [h0, h1, h2707, h2711, h4, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
              · linarith only [h2004, h2708, h4, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2719 | h2719
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2720 | h2720
                · linarith only [h2, h2005, h2720, hlam]
                · linarith only [h2707, h2719, h2720, hlam]
              · linarith only [h2004, h2719, h4, hc23, hlam, hphi, ht12, u1ehi2]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2724 | h2724
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2725 | h2725
      · linarith only [h0, h2725, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2727 | h2727
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2728 | h2728
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2729 | h2729
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2730 | h2730
              · linarith only [h1, h2004, h2730, hlam]
              · linarith only [h2725, h2728, h2730, hlam]
            · linarith only [h2725, h2727, h2729, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2734 | h2734
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2735 | h2735
              · linarith only [h0, h2004, h2727, h2735, h4, hc13, hlam, hphi, u1ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2737 | h2737
                · linarith only [h2725, h2727, h2735, h2737, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2739 | h2739
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2740 | h2740
                    · linarith only [h0, h2004, h2727, h2740, h4, hc23, hlam, hphi, ht12, u1ehi3]
                    · linarith only [h0, h2727, h2740, h4, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                  · linarith only [h0, h2727, h2739, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
            · linarith only [h2725, h2727, h2734, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2745 | h2745
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2746 | h2746
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2747 | h2747
              · linarith only [h1, h2004, h2747, hlam]
              · linarith only [h2727, h2745, h2746, h2747, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2750 | h2750
              · linarith only [h1, h2004, h2750, hlam]
              · linarith only [h2725, h2745, h2750, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2753 | h2753
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2754 | h2754
              · linarith only [h1, h2004, h2754, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2756 | h2756
                · linarith only [h2753, h2754, h2756, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2758 | h2758
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2759 | h2759
                    · linarith only [h1, h2004, h2727, h2753, h2759, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h0, h2759, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h0, h1, h2753, h2758, h4, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2763 | h2763
              · linarith only [h1, h2004, h2763, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2765 | h2765
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2766 | h2766
                  · linarith only [h2725, h2753, h2766, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h0, h2766, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2769 | h2769
                  · linarith only [h2725, h2753, h2769, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h0, h2769, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2772 | h2772
      · linarith only [h0, h2772, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2774 | h2774
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2775 | h2775
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2776 | h2776
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2777 | h2777
              · linarith only [h1, h2004, h2777, hlam]
              · linarith only [h2772, h2775, h2777, hlam]
            · linarith only [h2772, h2774, h2776, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2781 | h2781
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2782 | h2782
              · linarith only [h0, h2004, h2774, h2782, h4, hc13, hlam, hphi, u1ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2784 | h2784
                · linarith only [h2, h2724, h2784, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2786 | h2786
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2787 | h2787
                    · linarith only [h0, h2004, h2787, h4, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h0, h2774, h2787, h4, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                  · linarith only [h0, h2774, h2786, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
            · linarith only [h2772, h2774, h2781, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2792 | h2792
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2793 | h2793
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2794 | h2794
              · linarith only [h0, h2004, h2792, h2794, h4, hc13, hlam, hphi, u1ehi4]
              · linarith only [h2774, h2792, h2793, h2794, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2797 | h2797
              · linarith only [h1, h2004, h2797, hlam]
              · linarith only [h2772, h2792, h2797, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2800 | h2800
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2801 | h2801
              · linarith only [h1, h2004, h2801, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2803 | h2803
                · linarith only [h2, h2724, h2803, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2805 | h2805
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2806 | h2806
                    · linarith only [h1, h2004, h2774, h2800, h2806, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h0, h2806, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h0, h1, h2800, h2805, h4, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2810 | h2810
              · linarith only [h1, h2004, h2810, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2812 | h2812
                · linarith only [h2, h2724, h2812, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2814 | h2814
                  · linarith only [h2800, h2814, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h0, h2814, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 5626000 in
set_option maxHeartbeats 5626000 in
theorem r1l7_21_15_M_IR_L_I_s3 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_21_15_M_IR_L_I_s3_x0 m hb1 hb5 hg0 hg1 hg2 hg3 h4
  · exact r1l7_21_15_M_IR_L_I_s3_x1 m hb1 hb5 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 5630000 in
set_option maxHeartbeats 5630000 in
theorem r1l7_21_15_M_IR_L_I_s2 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_21_15_M_IR_L_I_s3 m hb1 hb5 h0 h1 h2 h3
  · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]

set_option maxHeartbeats 5634000 in
set_option maxHeartbeats 5634000 in
theorem r1l7_21_15_M_IR_L_I_s1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_21_15_M_IR_L_I_s2 m hb1 hb5 h0 h1 h2
  · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]

end R2N4
