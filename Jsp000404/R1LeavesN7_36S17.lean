import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2006 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2007 | h2007
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2008 | h2008
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2009 | h2009
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2010 | h2010
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2011 | h2011
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2012 | h2012
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2013 | h2013
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2014 | h2014
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2015 | h2015
                  · linarith only [h0, h2007, h2015, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h2006, h2012, h2014, h2015, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2018 | h2018
                  · linarith only [h0, h2007, h2018, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2020 | h2020
                    · linarith only [h0, h2006, h2012, h2014, h2020, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
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
                        linarith only [h0, hlam, p2022_1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2022_1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h0, h2007, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2022_1, u4ehi1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2022_1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2008, hc02, hc15, hlam, hphi, ht0b, ht5b, p2022_1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h0, h2013, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2022_1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h0, h2007, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2022_1, u4ehi1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h0, h2007, h2014, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2022_1, u4ehi1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2006, hlam, p2022_1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2009, hlam, p2022_1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2006, h2007, hc01, hlam, hphi, ht0b, ht45, ht5b, p2022_1, u4ehi1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h0, h2006, h2007, h2014, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2022_1, u4ehi1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2007, hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2010, hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2012, hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2014, hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2008, hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2011, hlam, p2022_1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2013, hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2007, hc05, hlam, hphi, ht0b, ht45, ht5b, p2022_1, u4ehi1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [hlam, p2022_0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2048 | h2048
                · linarith only [h2012, h2013, h2048, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2050 | h2050
                  · linarith only [h0, h2007, h2048, h2050, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2052 | h2052
                    · linarith only [h2012, h2013, h2048, h2052, hlam]
                    · linarith only [h2012, h2013, h2052, hc45, hlam, hphi, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2055 | h2055
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2056 | h2056
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2057 | h2057
                  · linarith only [h0, h2007, h2057, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h2007, h2056, h2057, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h2012, h2055, h2056, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2061 | h2061
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2062 | h2062
                  · linarith only [h0, h2007, h2062, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h2007, h2061, h2062, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2065 | h2065
                  · linarith only [h0, h2007, h2065, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2067 | h2067
                    · rcases h0bigk with h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [hlam, p2068_0]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h0, hlam, p2068_1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2068_1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h0, h2007, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2068_1, u4ehi1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h0, h2007, h2061, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2068_1, u4ehi1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p2068_1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [hlam, p2068_0]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        rcases p2068_3 (m.d 0 1) (by simp) with h2076 | h2076
                        · linarith only [h0, h2076, hlam]
                        · linarith only [h2006, h2076, hlam]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h0, h2007, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2068_1, u4ehi1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h0, h2007, h2061, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2068_1, u4ehi1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h2006, hlam, p2068_1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h2009, hlam, p2068_1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [hlam, p2068_0]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h2012, hlam, p2068_1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h2055, hlam, p2068_1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h2007, hlam, p2068_0]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h2010, hlam, p2068_0]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h2009, h2061, h2067, hc23, hc34, hlam, hphi, p2068_1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [hlam, p2068_0]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h2061, hlam, p2068_0]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h2008, hlam, p2068_0]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h2011, hlam, p2068_1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h0, h2007, h2008, h2009, h2061, h2067, hc12, hc23, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2068_1, u4ehi1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [h2007, h2061, h2067, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2068_1, u4ehi1]
                      · have p2068_0 := h2068c.1
                        have p2068_1 := h2068c.2.1
                        have p2068_2 := h2068c.2.2.1
                        have p2068_3 := h2068c.2.2.2
                        linarith only [hlam, p2068_0]
                    · rcases h0bigk with h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c | h2096c
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [hlam, p2096_0]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h0, hlam, p2096_1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h0, h2009, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2096_1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h0, h2007, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2096_1, u4ehi1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2096_1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p2096_1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [hlam, p2096_0]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        rcases p2096_3 (m.d 0 1) (by simp) with h2104 | h2104
                        · linarith only [h0, h2104, hlam]
                        · linarith only [h2006, h2104, hlam]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h0, h2007, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2096_1, u4ehi1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h0, h2008, h2065, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2096_1, u4ehi1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h2006, hlam, p2096_1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h2009, hlam, p2096_1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [hlam, p2096_0]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h2012, hlam, p2096_1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h2055, hlam, p2096_1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h2007, hlam, p2096_0]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h2010, hlam, p2096_0]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h0, h2007, h2009, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2096_1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [hlam, p2096_0]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h2061, hlam, p2096_0]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h2008, hlam, p2096_0]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h2011, hlam, p2096_1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h0, h2008, h2009, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2096_1]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [h0, h2008, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2096_1, u4ehi0]
                      · have p2096_0 := h2096c.1
                        have p2096_1 := h2096c.2.1
                        have p2096_2 := h2096c.2.2.1
                        have p2096_3 := h2096c.2.2.2
                        linarith only [hlam, p2096_0]
          · linarith only [h0, h2008, h2011, hlam]
        · linarith only [h0, h2007, h2010, hlam]
      · linarith only [h0, h2006, h2009, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2127 | h2127
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2128 | h2128
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2129 | h2129
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2130 | h2130
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2131 | h2131
              · linarith only [h2006, h2008, h2131, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2133 | h2133
                · linarith only [h2006, h2008, h2130, h2133, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2135 | h2135
                  · linarith only [h2007, h2133, h2135, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h2007, h2008, h2135, hc45, hlam, hphi, u4ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2138 | h2138
              · linarith only [h2007, h2008, h2130, h2138, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2140 | h2140
                · linarith only [h2007, h2008, h2140, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2142 | h2142
                  · linarith only [h2007, h2008, h2130, h2140, h2142, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h2007, h2008, h2142, hc45, hlam, hphi, u4ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2145 | h2145
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2146 | h2146
              · linarith only [h2006, h2008, h2146, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2148 | h2148
                · linarith only [h0, h2006, h2129, h2145, h2148, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2150 | h2150
                  · linarith only [h2007, h2148, h2150, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h2006, h2008, h2145, h2150, hc45, hlam, hphi, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2153 | h2153
              · linarith only [h2007, h2008, h2145, h2153, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2155 | h2155
                · linarith only [h0, h2007, h2129, h2155, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2157 | h2157
                  · linarith only [h0, h2007, h2155, h2157, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h2007, h2008, h2157, hc45, hlam, hphi, u4ehi1]
        · linarith only [h0, h2007, h2128, hlam]
      · linarith only [h0, h2006, h2127, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2162 | h2162
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2163 | h2163
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2164 | h2164
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2165 | h2165
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2166 | h2166
            · linarith only [h2006, h2007, h2166, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2168 | h2168
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2169 | h2169
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2170 | h2170
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2171 | h2171
                    · rcases h0bigk with h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [hlam, p2172_0]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h0, hlam, p2172_1]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2007, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2172_1]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2007, hlam, p2172_1]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2007, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p2172_1]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p2172_1]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [hlam, p2172_0]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h0, h2168, h2171, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2172_1, u4ehi4]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h0, h2006, h2007, h2168, h2171, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2172_1, u4ehi4]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h0, h2168, h2171, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2172_1, u4ehi4]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2006, hlam, p2172_1]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2163, hlam, p2172_1]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [hlam, p2172_0]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2166, hlam, p2172_1]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2166, h2168, h2171, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2172_1, u4ehi4]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2006, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2172_1]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2164, hlam, p2172_0]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2166, hc03, hc34, hlam, hphi, p2172_1]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [hlam, p2172_0]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2166, h2168, h2171, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2172_1, u4ehi4]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2162, hlam, p2172_0]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2165, hlam, p2172_1]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2168, hlam, p2172_0]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [h2169, hlam, p2172_1]
                      · have p2172_0 := h2172c.1
                        have p2172_1 := h2172c.2.1
                        have p2172_2 := h2172c.2.2.1
                        have p2172_3 := h2172c.2.2.2
                        linarith only [hlam, p2172_0]
                    · linarith only [h0, h2162, h2166, h2170, h2171, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h2006, h2007, h2170, hc13, hc45, hlam, hphi, ht34]
                · linarith only [h2007, h2162, h2169, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2201 | h2201
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2202 | h2202
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2203 | h2203
                    · rcases h0bigk with h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [hlam, p2204_0]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h0, hlam, p2204_1]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2204_1]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h2007, hlam, p2204_1]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2204_1]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h2006, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2204_1]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [hlam, p2204_0]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        rcases p2204_3 (m.d 0 1) (by simp) with h2212 | h2212
                        · linarith only [h0, h2212, hlam]
                        · linarith only [h2006, h2212, hlam]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h0, h2007, h2162, h2202, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2204_1, u4ehi4]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h0, h2162, h2202, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2204_1, u4ehi4]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h2006, hlam, p2204_1]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h2163, hlam, p2204_1]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [hlam, p2204_0]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h2166, hlam, p2204_1]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h2168, hlam, p2204_1]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h2162, h2202, hc04, hlam, hphi, ht0b, ht45, ht5b, p2204_1, u4ehi4]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h2164, hlam, p2204_0]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h2006, h2166, hc13, hc34, hlam, hphi, p2204_1]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [hlam, p2204_0]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h2162, h2166, h2202, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2204_1, u4ehi4]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h2162, hlam, p2204_0]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h2165, hlam, p2204_1]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h0, h2006, h2162, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2204_1]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [h2201, hlam, p2204_1]
                      · have p2204_0 := h2204c.1
                        have p2204_1 := h2204c.2.1
                        have p2204_2 := h2204c.2.2.1
                        have p2204_3 := h2204c.2.2.2
                        linarith only [hlam, p2204_0]
                    · linarith only [h2166, h2201, h2203, hlam]
                  · linarith only [h2007, h2162, h2201, h2202, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h2007, h2162, h2201, hlam]
          · linarith only [h0, h2162, h2165, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2236 | h2236
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2237 | h2237
            · linarith only [h0, h2006, h2164, h2237, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2239 | h2239
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2240 | h2240
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2241 | h2241
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2242 | h2242
                    · rcases h0bigk with h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [hlam, p2243_0]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h0, hlam, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2007, hlam, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h0, h2164, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2164, hc01, hc24, hlam, hphi, ht12, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [hlam, p2243_0]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2164, h2239, h2242, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2243_1, u4ehi4]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2164, hlam, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2162, h2164, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2006, hlam, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2163, hlam, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [hlam, p2243_0]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2237, hlam, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2162, h2237, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2006, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h0, h2006, h2164, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2237, hc03, hc34, hlam, hphi, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [hlam, p2243_0]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2237, h2239, h2242, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2243_1, u4ehi4]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2162, hlam, p2243_0]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2236, hlam, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2239, hlam, p2243_0]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [h2240, hlam, p2243_1]
                      · have p2243_0 := h2243c.1
                        have p2243_1 := h2243c.2.1
                        have p2243_2 := h2243c.2.2.1
                        have p2243_3 := h2243c.2.2.2
                        linarith only [hlam, p2243_0]
                    · linarith only [h0, h2162, h2237, h2241, h2242, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h2006, h2007, h2241, hc13, hc45, hlam, hphi, ht34]
                · linarith only [h0, h2006, h2164, h2239, h2240, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2272 | h2272
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2273 | h2273
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2274 | h2274
                    · rcases h0bigk with h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [hlam, p2275_0]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h0, hlam, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2007, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2007, hlam, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2007, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2006, h2164, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [hlam, p2275_0]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2006, h2164, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2164, hlam, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2162, h2164, h2273, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2275_1, u4ehi4]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2006, hlam, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2163, hlam, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [hlam, p2275_0]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2237, hlam, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2239, hlam, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2162, h2164, h2273, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2275_1, u4ehi4]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2164, hc02, hc24, hlam, hphi, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2006, h2237, hc13, hc34, hlam, hphi, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [hlam, p2275_0]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2162, h2237, h2273, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2275_1, u4ehi4]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2162, hlam, p2275_0]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2236, hlam, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h0, h2006, h2162, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [h2272, hlam, p2275_1]
                      · have p2275_0 := h2275c.1
                        have p2275_1 := h2275c.2.1
                        have p2275_2 := h2275c.2.2.1
                        have p2275_3 := h2275c.2.2.2
                        linarith only [hlam, p2275_0]
                    · linarith only [h2237, h2272, h2274, hlam]
                  · linarith only [h2007, h2237, h2272, h2273, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h2007, h2162, h2272, hlam]
          · linarith only [h0, h2162, h2236, hlam]
      · linarith only [h0, h2006, h2163, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2306 | h2306
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2307 | h2307
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2308 | h2308
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2309 | h2309
            · linarith only [h2006, h2007, h2309, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2311 | h2311
              · linarith only [h2006, h2162, h2311, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2313 | h2313
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2314 | h2314
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2315 | h2315
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
                        linarith only [h0, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2007, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2162, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        rcases p2316_3 (m.d 0 1) (by simp) with h2324 | h2324
                        · linarith only [h0, h2324, hlam]
                        · linarith only [h2006, h2324, hlam]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, h2313, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2316_1, u4ehi4]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, h2006, h2162, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2006, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2306, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2309, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2311, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2006, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2307, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2006, h2309, hc13, hc34, hlam, hphi, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2006, h2162, h2309, hc13, hc34, hlam, hphi, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2006, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2308, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2006, h2311, hc13, hc35, hlam, hphi, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2313, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                    · linarith only [h2309, h2313, h2315, hlam]
                  · linarith only [h2006, h2007, h2309, h2313, h2314, hc13, hc34, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2346 | h2346
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2347 | h2347
                    · linarith only [h2006, h2007, h2313, h2347, hc13, hc34, hlam, hphi]
                    · rcases h0bigk with h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [hlam, p2349_0]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h0, hlam, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2006, h2007, h2309, h2346, h2347, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2007, hlam, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2162, hlam, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [hlam, p2349_0]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        rcases p2349_3 (m.d 0 1) (by simp) with h2357 | h2357
                        · linarith only [h0, h2357, hlam]
                        · linarith only [h2006, h2357, hlam]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2349_1, u4ehi0]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h0, h2006, h2162, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2006, hlam, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2306, hlam, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [hlam, p2349_0]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2309, hlam, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2311, hlam, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2006, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2307, hlam, p2349_0]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2309, h2346, h2347, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [hlam, p2349_0]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2313, hlam, p2349_0]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2006, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2308, hlam, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2306, h2311, h2346, h2347, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2349_1]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [h2311, h2346, h2347, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2349_1, u4ehi0]
                      · have p2349_0 := h2349c.1
                        have p2349_1 := h2349c.2.1
                        have p2349_2 := h2349c.2.2.1
                        have p2349_3 := h2349c.2.2.2
                        linarith only [hlam, p2349_0]
                  · linarith only [h2006, h2007, h2346, hc13, hc45, hlam, hphi, ht34]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2378 | h2378
            · linarith only [h2006, h2007, h2378, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2380 | h2380
              · linarith only [h0, h2006, h2308, h2380, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2382 | h2382
                · linarith only [h2307, h2308, h2382, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2384 | h2384
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2385 | h2385
                    · linarith only [h2006, h2007, h2382, h2385, hc13, hc34, hlam, hphi]
                    · rcases h0bigk with h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [hlam, p2387_0]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h0, hlam, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2006, h2007, h2378, h2384, h2385, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2007, hlam, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2162, hlam, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2308, h2380, hc01, hc35, hlam, hphi, ht12, ht23, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [hlam, p2387_0]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2006, h2308, h2380, hc13, hc35, hlam, hphi, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2006, h2007, h2308, h2380, hc13, hc35, hlam, hphi, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2308, hlam, p2387_0]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2006, hlam, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2306, hlam, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [hlam, p2387_0]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2378, hlam, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2380, hlam, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2006, h2378, h2384, h2385, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2307, hlam, p2387_0]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2006, h2378, h2384, h2385, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [hlam, p2387_0]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2382, hlam, p2387_0]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2006, h2380, hc13, hc35, hlam, hphi, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2380, hc02, hc35, hlam, hphi, ht23, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2006, h2380, hc13, hc35, hlam, hphi, p2387_1]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [h2382, h2384, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2387_1, u4ehi0]
                      · have p2387_0 := h2387c.1
                        have p2387_1 := h2387c.2.1
                        have p2387_2 := h2387c.2.2.1
                        have p2387_3 := h2387c.2.2.2
                        linarith only [hlam, p2387_0]
                  · linarith only [h2006, h2007, h2384, hc13, hc45, hlam, hphi, ht34]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2414 | h2414
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2415 | h2415
            · linarith only [h0, h2006, h2307, h2415, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2417 | h2417
              · linarith only [h2006, h2162, h2417, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2419 | h2419
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2420 | h2420
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2421 | h2421
                    · rcases h0bigk with h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [hlam, p2422_0]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h0, hlam, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2007, hlam, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2162, hlam, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [hlam, p2422_0]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2006, h2307, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2307, hlam, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2006, h2162, h2307, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2006, hlam, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2306, hlam, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [hlam, p2422_0]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2415, hlam, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2417, hlam, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2006, h2307, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2307, hc02, hc24, hlam, hphi, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2006, h2415, hc13, hc34, hlam, hphi, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [hlam, p2422_0]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2006, h2162, h2415, hc13, hc34, hlam, hphi, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2006, h2414, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2414, hlam, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2006, h2307, h2414, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [h2419, hlam, p2422_1]
                      · have p2422_0 := h2422c.1
                        have p2422_1 := h2422c.2.1
                        have p2422_2 := h2422c.2.2.1
                        have p2422_3 := h2422c.2.2.2
                        linarith only [hlam, p2422_0]
                    · linarith only [h2415, h2419, h2421, hlam]
                  · linarith only [h2006, h2007, h2415, h2419, h2420, hc13, hc34, hlam, hphi]
                · linarith only [h2307, h2414, h2419, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2451 | h2451
            · linarith only [h0, h2006, h2307, h2451, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2453 | h2453
              · linarith only [h0, h2006, h2414, h2453, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2455 | h2455
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2456 | h2456
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2457 | h2457
                    · rcases h0bigk with h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [hlam, p2458_0]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h0, hlam, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2162, h2456, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2007, hlam, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2162, hlam, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2414, hc01, hc25, hlam, hphi, ht12, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [hlam, p2458_0]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2006, h2414, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2307, hlam, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2414, hlam, p2458_0]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2006, hlam, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2306, hlam, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [hlam, p2458_0]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2451, hlam, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2453, hlam, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2006, h2007, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2307, hc02, hc24, hlam, hphi, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2006, h2451, hc13, hc34, hlam, hphi, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [hlam, p2458_0]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2006, h2162, h2451, hc13, hc34, hlam, hphi, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2006, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h0, h2006, h2414, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2006, h2453, hc13, hc35, hlam, hphi, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [h2455, hlam, p2458_1]
                      · have p2458_0 := h2458c.1
                        have p2458_1 := h2458c.2.1
                        have p2458_2 := h2458c.2.2.1
                        have p2458_3 := h2458c.2.2.2
                        linarith only [hlam, p2458_0]
                    · linarith only [h2451, h2455, h2457, hlam]
                  · linarith only [h2006, h2007, h2451, h2455, h2456, hc13, hc34, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2486 | h2486
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2487 | h2487
                    · linarith only [h2006, h2007, h2455, h2487, hc13, hc34, hlam, hphi]
                    · rcases h0bigk with h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [hlam, p2489_0]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h0, hlam, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h0, h2006, h2307, h2451, hc13, hc34, hlam, hphi, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2007, hlam, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2162, hlam, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2307, h2451, hc01, hc34, hlam, hphi, ht12, ht23, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [hlam, p2489_0]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2006, h2307, h2451, h2487, hc13, hc45, hlam, hphi, ht34, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2307, hlam, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2414, hlam, p2489_0]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2006, hlam, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2306, hlam, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [hlam, p2489_0]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2451, hlam, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2453, hlam, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2006, h2451, h2487, hc13, hc45, hlam, hphi, ht34, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2451, h2487, hc02, hc45, hlam, hphi, ht23, ht34, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2006, h2451, h2487, hc13, hc45, hlam, hphi, ht34, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [hlam, p2489_0]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2455, hlam, p2489_0]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2006, h2414, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h0, h2006, h2414, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2006, h2453, hc13, hc35, hlam, hphi, p2489_1]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [h2455, hc45, hlam, hphi, p2489_1, u4ehi0]
                      · have p2489_0 := h2489c.1
                        have p2489_1 := h2489c.2.1
                        have p2489_2 := h2489c.2.2.1
                        have p2489_3 := h2489c.2.2.2
                        linarith only [hlam, p2489_0]
                  · linarith only [h2006, h2007, h2486, hc13, hc45, hlam, hphi, ht34]
      · linarith only [h0, h2006, h2306, hlam]

set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2006 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2517 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2518 | h2518
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2519 | h2519
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2520 | h2520
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2521 | h2521
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2522 | h2522
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2523 | h2523
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2524 | h2524
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2525 | h2525
                · linarith only [h2006, h2517, h2525, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h2006, h2517, h2524, h2525, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2528 | h2528
                · linarith only [h2006, h2517, h2524, h2528, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2530 | h2530
                  · linarith only [h2522, h2524, h2530, hlam]
                  · rcases h0bigk with h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [hlam, p2532_0]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h0, hlam, p2532_1]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2006, hlam, p2532_0]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2006, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p2532_1, u4ehi0]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2006, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p2532_1]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2518, h2528, hc02, hlam, hphi, ht0b, ht45, ht5b, p2532_1, u4ehi1]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [hlam, p2532_0]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h0, h2006, h2518, h2528, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2532_1, u4ehi1]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h0, h2520, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2532_1, u4ehi2]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h0, h2518, h2528, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2532_1, u4ehi1]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2518, h2528, hc03, hlam, hphi, ht0b, ht45, ht5b, p2532_1, u4ehi1]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2519, hlam, p2532_1]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [hlam, p2532_0]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h0, h2519, h2520, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2532_1, u4ehi2]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h0, h2518, h2519, h2528, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2532_1, u4ehi1]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2517, hlam, p2532_0]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2520, hlam, p2532_0]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2522, hlam, p2532_0]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [hlam, p2532_0]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2524, hlam, p2532_0]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2518, hlam, p2532_0]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2521, hlam, p2532_1]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2523, hlam, p2532_0]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [h2520, hc05, hlam, hphi, ht0b, ht45, ht5b, p2532_1, u4ehi2]
                    · have p2532_0 := h2532c.1
                      have p2532_1 := h2532c.2.1
                      have p2532_2 := h2532c.2.2.1
                      have p2532_3 := h2532c.2.2.2
                      linarith only [hlam, p2532_0]
            · linarith only [h2006, h2518, h2523, hlam]
          · linarith only [h2006, h2517, h2522, hlam]
        · linarith only [h0, h2518, h2521, hlam]
      · linarith only [h2006, h2517, h2519, h2520, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2562 | h2562
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2563 | h2563
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2564 | h2564
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2565 | h2565
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2566 | h2566
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2567 | h2567
                · linarith only [h0, h2517, h2567, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h0, h2517, h2519, h2566, h2567, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2570 | h2570
                · linarith only [h0, h2517, h2519, h2566, h2570, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2572 | h2572
                  · linarith only [h2564, h2566, h2572, hlam]
                  · rcases h0bigk with h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c | h2574c
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [hlam, p2574_0]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h0, hlam, p2574_1]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2006, hlam, p2574_0]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h0, h2519, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2574_1, u4ehi0]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h0, h2519, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2574_1]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2519, hc01, hc23, hlam, hphi, ht12, p2574_1]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [hlam, p2574_0]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2519, hlam, p2574_0]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2517, h2519, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2574_1, u4ehi1]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2518, h2519, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2574_1]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2517, hc03, hlam, hphi, ht0b, ht45, ht5b, p2574_1, u4ehi1]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2519, hc02, hc23, hlam, hphi, p2574_1]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [hlam, p2574_0]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2517, h2519, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2574_1, u4ehi1]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2517, h2519, h2566, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2574_1, u4ehi1]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2517, hlam, p2574_0]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2562, hlam, p2574_0]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2564, hlam, p2574_0]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [hlam, p2574_0]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2566, hlam, p2574_0]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2518, hlam, p2574_0]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2563, hlam, p2574_1]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2565, hlam, p2574_0]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [h2517, hc05, hlam, hphi, ht0b, ht45, ht5b, p2574_1, u4ehi1]
                    · have p2574_0 := h2574c.1
                      have p2574_1 := h2574c.2.1
                      have p2574_2 := h2574c.2.2.1
                      have p2574_3 := h2574c.2.2.2
                      linarith only [hlam, p2574_0]
            · linarith only [h2006, h2518, h2565, hlam]
          · linarith only [h0, h2517, h2519, h2564, hlam]
        · linarith only [h0, h2518, h2563, hlam]
      · linarith only [h0, h2517, h2562, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2604 | h2604
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2605 | h2605
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2606 | h2606
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2607 | h2607
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2608 | h2608
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2609 | h2609
              · linarith only [h2517, h2518, h2609, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2611 | h2611
                · linarith only [h2517, h2518, h2609, h2611, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                · linarith only [h2517, h2518, h2611, hc45, hlam, hphi, u4ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2614 | h2614
              · linarith only [h2517, h2518, h2614, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2616 | h2616
                · linarith only [h2517, h2614, h2616, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · linarith only [h2517, h2518, h2616, hc45, hlam, hphi, u4ehi1]
          · linarith only [h2006, h2517, h2607, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2620 | h2620
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2621 | h2621
            · linarith only [h2604, h2606, h2621, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2623 | h2623
              · linarith only [h0, h2517, h2606, h2623, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2625 | h2625
                · linarith only [h2006, h2517, h2604, h2606, h2623, h2625, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                · linarith only [h2517, h2518, h2625, hc45, hlam, hphi, u4ehi1]
          · linarith only [h2006, h2517, h2620, hlam]
      · linarith only [h2006, h2517, h2604, h2605, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2630 | h2630
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2631 | h2631
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2632 | h2632
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2633 | h2633
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2634 | h2634
              · linarith only [h2517, h2518, h2634, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2636 | h2636
                · linarith only [h2517, h2634, h2636, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · linarith only [h2517, h2518, h2636, hc45, hlam, hphi, u4ehi1]
            · linarith only [h2604, h2631, h2633, hlam]
          · linarith only [h0, h2517, h2604, h2632, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2641 | h2641
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2642 | h2642
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2643 | h2643
              · linarith only [h0, h2517, h2631, h2643, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2645 | h2645
                · linarith only [h0, h2517, h2604, h2643, h2645, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                · linarith only [h2517, h2518, h2645, hc45, hlam, hphi, u4ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2648 | h2648
              · linarith only [h0, h2517, h2604, h2642, h2648, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2650 | h2650
                · linarith only [h0, h2517, h2604, h2642, h2648, h2650, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                · linarith only [h2517, h2518, h2650, hc45, hlam, hphi, u4ehi1]
          · linarith only [h0, h2517, h2604, h2641, hlam]
      · linarith only [h0, h2517, h2630, hlam]

end R2N4
