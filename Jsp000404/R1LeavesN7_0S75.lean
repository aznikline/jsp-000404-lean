import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h43122 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h43123 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h43124 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h43125 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 1 3 5 (by decide) (by decide) with h43126 | h43126
  · rcases m.htr 1 4 5 (by decide) (by decide) with h43127 | h43127
    · rcases m.htr 2 3 4 (by decide) (by decide) with h43128 | h43128
      · rcases m.htr 2 3 5 (by decide) (by decide) with h43129 | h43129
        · rcases m.htr 2 4 5 (by decide) (by decide) with h43130 | h43130
          · linarith only [h41028, h41032, h43130, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h43132 | h43132
            · linarith only [h41028, h41032, h43128, h43132, hlam]
            · rcases h1bigk with h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c | h43134c
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h0, hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h33187, hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h36828, hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h39227, hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                rcases p43134_3 (m.d 0 1) (by simp) with h43140 | h43140
                · linarith only [h43140, hlam, p43134_0]
                · rcases p43134_3 (m.d 1 2) (by simp) with h43142 | h43142
                  · rcases p43134_3 (m.d 1 3) (by simp) with h43143 | h43143
                    · linarith only [h43122, h43143, hlam]
                    · linarith only [h33187, h43143, hlam]
                  · linarith only [h43142, hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h36828, h41032, h43125, h43127, hc01, hc12, hlam, hphi, p43134_1]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h36828, h41032, h43127, hc01, hc12, hlam, hphi, p43134_1]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h39227, hc01, hc12, hlam, hphi, p43134_1]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                rcases p43134_3 (m.d 0 1) (by simp) with h43151 | h43151
                · linarith only [h43151, hlam, p43134_0]
                · rcases p43134_3 (m.d 1 2) (by simp) with h43153 | h43153
                  · rcases p43134_3 (m.d 1 3) (by simp) with h43154 | h43154
                    · rcases p43134_3 (m.d 1 4) (by simp) with h43155 | h43155
                      · linarith only [h43125, h43155, hlam]
                      · linarith only [h36828, h43155, hlam]
                    · linarith only [h43154, hlam, p43134_0]
                  · linarith only [h0, h43153, hlam]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h43122, hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h36828, h41032, h43127, hc01, hc13, hlam, hphi, p43134_1]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h36828, h41032, h43122, h43127, hc01, hc12, hlam, hphi, p43134_1]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                rcases p43134_3 (m.d 0 1) (by simp) with h43164 | h43164
                · linarith only [h43164, hlam, p43134_0]
                · rcases p43134_3 (m.d 1 2) (by simp) with h43166 | h43166
                  · rcases p43134_3 (m.d 1 3) (by simp) with h43167 | h43167
                    · rcases p43134_3 (m.d 1 4) (by simp) with h43168 | h43168
                      · rcases p43134_3 (m.d 1 5) (by simp) with h43169 | h43169
                        · linarith only [h43127, h43169, hlam]
                        · linarith only [h39227, h43169, hlam]
                      · linarith only [h43168, hlam, p43134_0]
                    · linarith only [h33187, h43167, hlam]
                  · linarith only [h0, h43166, hlam]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h43123, hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h43125, hlam, p43134_1]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h36828, h41032, h43127, hc01, hc14, hlam, hphi, p43134_1]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                rcases p43134_3 (m.d 0 1) (by simp) with h43179 | h43179
                · linarith only [h43179, hlam, p43134_0]
                · rcases p43134_3 (m.d 1 2) (by simp) with h43181 | h43181
                  · rcases p43134_3 (m.d 1 3) (by simp) with h43182 | h43182
                    · rcases p43134_3 (m.d 1 4) (by simp) with h43183 | h43183
                      · rcases p43134_3 (m.d 1 5) (by simp) with h43184 | h43184
                        · rcases h1emax with h43185 | h43185 | h43185 | h43185 | h43185
                          · rcases h2bigk with h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c | h43186c
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [h0, hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              rcases p43186_3 (m.d 0 2) (by simp) with h43189 | h43189
                              · rcases p43186_3 (m.d 1 2) (by simp) with h43190 | h43190
                                · rcases p43186_3 (m.d 2 3) (by simp) with h43191 | h43191
                                  · linarith only [h43191, hlam, p43186_0]
                                  · rcases p43186_3 (m.d 2 4) (by simp) with h43193 | h43193
                                    · linarith only [h41028, h43193, hlam]
                                    · rcases p43186_3 (m.d 2 5) (by simp) with h43195 | h43195
                                      · linarith only [h41029, h43195, hlam]
                                      · rcases h4bigk with h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c | h43197c
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [hlam, p43197_0]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h36828, hlam, p43197_1]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h41032, hc24, hc45, hlam, hphi, p43197_1]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h41032, hc34, hc45, hlam, hphi, p43197_1]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h41032, hlam, p43197_0]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          rcases p43197_3 (m.d 0 4) (by simp) with h43203 | h43203
                                          · linarith only [h36828, h43203, hlam]
                                          · rcases p43197_3 (m.d 1 4) (by simp) with h43205 | h43205
                                            · rcases p43197_3 (m.d 2 4) (by simp) with h43206 | h43206
                                              · linarith only [h43123, h43206, hlam]
                                              · rcases p43197_3 (m.d 3 4) (by simp) with h43208 | h43208
                                                · linarith only [h43125, h43208, hlam]
                                                · rcases p43197_3 (m.d 4 5) (by simp) with h43210 | h43210
                                                  · linarith only [h43127, h43210, hlam]
                                                  · linarith only [h41032, h43210, hlam]
                                            · linarith only [h36828, h43205, hlam]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [hlam, p43197_0]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          rcases p43197_3 (m.d 0 4) (by simp) with h43215 | h43215
                                          · linarith only [h36828, h43215, hlam]
                                          · linarith only [h41028, h43215, hlam]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          rcases p43197_3 (m.d 0 4) (by simp) with h43218 | h43218
                                          · linarith only [h36828, h43218, hlam]
                                          · linarith only [h41030, h43218, hlam]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h36828, h41032, hc01, hc14, hlam, hphi, p43197_1]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h41028, hlam, p43197_0]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h43123, hlam, p43197_0]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [hlam, p43197_0]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h41028, h41032, hc34, hc45, hlam, hphi, p43197_1]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h43130, hlam, p43197_0]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h41030, hlam, p43197_0]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h43125, hlam, p43197_0]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h43128, hlam, p43197_0]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [hlam, p43197_0]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h43132, hlam, p43197_0]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h36828, h43122, h43125, h43127, hc01, hc12, hlam, hphi, p43197_1]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [h43127, hlam, p43197_0]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          rcases p43197_3 (m.d 0 4) (by simp) with h43234 | h43234
                                          · linarith only [h41032, h43234, hlam]
                                          · linarith only [h41028, h43234, hlam]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          rcases p43197_3 (m.d 0 4) (by simp) with h43237 | h43237
                                          · linarith only [h41032, h43237, hlam]
                                          · linarith only [h41030, h43237, hlam]
                                        · have p43197_0 := h43197c.1
                                          have p43197_1 := h43197c.2.1
                                          have p43197_2 := h43197c.2.2.1
                                          have p43197_3 := h43197c.2.2.2
                                          linarith only [hlam, p43197_0]
                                · linarith only [h43122, h43190, hlam]
                              · linarith only [h43189, hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              rcases p43186_3 (m.d 0 2) (by simp) with h43243 | h43243
                              · rcases p43186_3 (m.d 1 2) (by simp) with h43244 | h43244
                                · rcases p43186_3 (m.d 2 3) (by simp) with h43245 | h43245
                                  · linarith only [h41027, h43245, hlam]
                                  · linarith only [h43128, h43245, hlam]
                                · linarith only [h43123, h43244, hlam]
                              · linarith only [h43243, hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              rcases p43186_3 (m.d 0 2) (by simp) with h43250 | h43250
                              · rcases p43186_3 (m.d 1 2) (by simp) with h43251 | h43251
                                · rcases p43186_3 (m.d 2 3) (by simp) with h43252 | h43252
                                  · linarith only [h41027, h43252, hlam]
                                  · linarith only [h43129, h43252, hlam]
                                · linarith only [h43124, h43251, hlam]
                              · linarith only [h43250, hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [h41027, h43129, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p43186_1]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              rcases p43186_3 (m.d 0 2) (by simp) with h43259 | h43259
                              · linarith only [h0, h43259, hlam]
                              · linarith only [h41027, h43259, hlam]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              rcases p43186_3 (m.d 0 2) (by simp) with h43262 | h43262
                              · linarith only [h0, h43262, hlam]
                              · linarith only [h41028, h43262, hlam]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              rcases p43186_3 (m.d 0 2) (by simp) with h43265 | h43265
                              · linarith only [h0, h43265, hlam]
                              · linarith only [h41029, h43265, hlam]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [h41027, hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [h43122, hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              rcases p43186_3 (m.d 0 2) (by simp) with h43271 | h43271
                              · rcases p43186_3 (m.d 1 2) (by simp) with h43272 | h43272
                                · rcases p43186_3 (m.d 2 3) (by simp) with h43273 | h43273
                                  · rcases p43186_3 (m.d 2 4) (by simp) with h43274 | h43274
                                    · linarith only [h43128, h43274, hlam]
                                    · rcases p43186_3 (m.d 2 5) (by simp) with h43276 | h43276
                                      · linarith only [h43129, h43276, hlam]
                                      · linarith only [h43130, h43276, hlam]
                                  · linarith only [h43128, h43273, hlam]
                                · linarith only [h43123, h43272, hlam]
                              · linarith only [h41028, h43271, hlam]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              rcases p43186_3 (m.d 0 2) (by simp) with h43282 | h43282
                              · rcases p43186_3 (m.d 1 2) (by simp) with h43283 | h43283
                                · rcases p43186_3 (m.d 2 3) (by simp) with h43284 | h43284
                                  · rcases p43186_3 (m.d 2 4) (by simp) with h43285 | h43285
                                    · linarith only [h43128, h43285, hlam]
                                    · rcases p43186_3 (m.d 2 5) (by simp) with h43287 | h43287
                                      · linarith only [h43129, h43287, hlam]
                                      · rcases h4bigk with h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c | h43289c
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [hlam, p43289_0]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h36828, hlam, p43289_1]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h41032, h43122, h43125, h43127, h43128, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43289_1]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h41032, h43122, h43125, h43127, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43289_1]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h41032, hlam, p43289_0]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          rcases p43289_3 (m.d 0 4) (by simp) with h43295 | h43295
                                          · linarith only [h36828, h43295, hlam]
                                          · rcases p43289_3 (m.d 1 4) (by simp) with h43297 | h43297
                                            · rcases p43289_3 (m.d 2 4) (by simp) with h43298 | h43298
                                              · linarith only [h43123, h43298, hlam]
                                              · rcases p43289_3 (m.d 3 4) (by simp) with h43300 | h43300
                                                · linarith only [h43125, h43300, hlam]
                                                · rcases p43289_3 (m.d 4 5) (by simp) with h43302 | h43302
                                                  · linarith only [h43127, h43302, hlam]
                                                  · linarith only [h41032, h43302, hlam]
                                            · linarith only [h36828, h43297, hlam]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [hlam, p43289_0]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          rcases p43289_3 (m.d 0 4) (by simp) with h43307 | h43307
                                          · linarith only [h36828, h43307, hlam]
                                          · linarith only [h41028, h43307, hlam]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          rcases p43289_3 (m.d 0 4) (by simp) with h43310 | h43310
                                          · linarith only [h36828, h43310, hlam]
                                          · linarith only [h41030, h43310, hlam]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h36828, h41032, hc01, hc14, hlam, hphi, p43289_1]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h41028, hlam, p43289_0]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h43123, hlam, p43289_0]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [hlam, p43289_0]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h0, h41027, h43130, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43186_1, p43289_1]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h43130, hlam, p43289_0]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h41030, hlam, p43289_0]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h43125, hlam, p43289_0]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h43128, hlam, p43289_0]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [hlam, p43289_0]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h43132, hlam, p43289_0]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h36828, h43122, h43125, h43127, hc01, hc12, hlam, hphi, p43289_1]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [h43127, hlam, p43289_0]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          rcases p43289_3 (m.d 0 4) (by simp) with h43326 | h43326
                                          · linarith only [h41032, h43326, hlam]
                                          · linarith only [h41028, h43326, hlam]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          rcases p43289_3 (m.d 0 4) (by simp) with h43329 | h43329
                                          · linarith only [h41032, h43329, hlam]
                                          · linarith only [h41030, h43329, hlam]
                                        · have p43289_0 := h43289c.1
                                          have p43289_1 := h43289c.2.1
                                          have p43289_2 := h43289c.2.2.1
                                          have p43289_3 := h43289c.2.2.2
                                          linarith only [hlam, p43289_0]
                                  · linarith only [h43129, h43284, hlam]
                                · linarith only [h43124, h43283, hlam]
                              · linarith only [h41029, h43282, hlam]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [h41028, hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [h43123, hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [h43128, hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [h43130, hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [h41029, hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [h43124, hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [h43129, hlam, p43186_0]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              rcases p43186_3 (m.d 0 2) (by simp) with h43344 | h43344
                              · rcases p43186_3 (m.d 1 2) (by simp) with h43345 | h43345
                                · rcases p43186_3 (m.d 2 3) (by simp) with h43346 | h43346
                                  · rcases p43186_3 (m.d 2 4) (by simp) with h43347 | h43347
                                    · linarith only [h43130, h43347, hlam]
                                    · rcases p43186_3 (m.d 2 5) (by simp) with h43349 | h43349
                                      · rcases h4bigk with h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c | h43350c
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [hlam, p43350_0]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h36828, hlam, p43350_1]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h41032, h43122, h43125, h43127, h43128, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43350_1]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h41032, h43122, h43125, h43127, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43350_1]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h41032, hlam, p43350_0]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          rcases p43350_3 (m.d 0 4) (by simp) with h43356 | h43356
                                          · linarith only [h36828, h43356, hlam]
                                          · rcases p43350_3 (m.d 1 4) (by simp) with h43358 | h43358
                                            · rcases p43350_3 (m.d 2 4) (by simp) with h43359 | h43359
                                              · linarith only [h43123, h43359, hlam]
                                              · rcases p43350_3 (m.d 3 4) (by simp) with h43361 | h43361
                                                · linarith only [h43125, h43361, hlam]
                                                · rcases p43350_3 (m.d 4 5) (by simp) with h43363 | h43363
                                                  · linarith only [h43127, h43363, hlam]
                                                  · linarith only [h41032, h43363, hlam]
                                            · linarith only [h36828, h43358, hlam]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [hlam, p43350_0]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h41029, h41032, h43127, hlam, p43186_1, p43350_2]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h41029, h41032, h43127, h43128, hlam, p43186_1, p43350_2]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h41029, h41032, h43122, h43125, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p43186_1, p43350_1]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h41028, hlam, p43350_0]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h43123, hlam, p43350_0]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [hlam, p43350_0]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h41029, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p43186_1, p43350_1]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h43130, hlam, p43350_0]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h41030, hlam, p43350_0]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h43125, hlam, p43350_0]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h43128, hlam, p43350_0]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [hlam, p43350_0]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h43132, hlam, p43350_0]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h36828, h43122, h43125, h43127, hc01, hc12, hlam, hphi, p43350_1]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [h43127, hlam, p43350_0]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          rcases p43350_3 (m.d 0 4) (by simp) with h43383 | h43383
                                          · linarith only [h41032, h43383, hlam]
                                          · linarith only [h41028, h43383, hlam]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          rcases p43350_3 (m.d 0 4) (by simp) with h43386 | h43386
                                          · linarith only [h41032, h43386, hlam]
                                          · linarith only [h41030, h43386, hlam]
                                        · have p43350_0 := h43350c.1
                                          have p43350_1 := h43350c.2.1
                                          have p43350_2 := h43350c.2.2.1
                                          have p43350_3 := h43350c.2.2.2
                                          linarith only [hlam, p43350_0]
                                      · linarith only [h43130, h43349, hlam]
                                  · linarith only [h43128, h43346, hlam]
                                · linarith only [h43123, h43345, hlam]
                              · linarith only [h41028, h43344, hlam]
                            · have p43186_0 := h43186c.1
                              have p43186_1 := h43186c.2.1
                              have p43186_2 := h43186c.2.2.1
                              have p43186_3 := h43186c.2.2.2
                              linarith only [hlam, p43186_0]
                          · linarith only [h0, h43185, hc01, hlam]
                          · linarith only [h43125, h43127, h43185, hc01, hlam, p43134_1]
                          · linarith only [h43127, h43185, hc01, hlam, p43134_1]
                          · linarith only [h43185, hc01, hlam, p43134_1]
                        · linarith only [h43184, hlam, p43134_0]
                      · linarith only [h36828, h43183, hlam]
                    · linarith only [h33187, h43182, hlam]
                  · linarith only [h0, h43181, hlam]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h43124, hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h43126, hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [h43127, hlam, p43134_0]
              · have p43134_0 := h43134c.1
                have p43134_1 := h43134c.2.1
                have p43134_2 := h43134c.2.2.1
                have p43134_3 := h43134c.2.2.2
                linarith only [hlam, p43134_0]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h43407 | h43407
          · linarith only [h41028, h41031, h41032, h43128, h43129, h43407, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h43409 | h43409
            · linarith only [h41031, h41032, h43128, h43129, h43409, hlam]
            · rcases h1bigk with h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c | h43411c
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h0, hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h33187, hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h36828, hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h39227, hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                rcases p43411_3 (m.d 0 1) (by simp) with h43417 | h43417
                · linarith only [h43417, hlam, p43411_0]
                · rcases p43411_3 (m.d 1 2) (by simp) with h43419 | h43419
                  · rcases p43411_3 (m.d 1 3) (by simp) with h43420 | h43420
                    · linarith only [h43122, h43420, hlam]
                    · linarith only [h33187, h43420, hlam]
                  · linarith only [h43419, hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h33187, hc01, hc12, hlam, hphi, p43411_1]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h41031, h41032, h43127, h43128, h43129, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43411_1]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h39227, hc01, hc12, hlam, hphi, p43411_1]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                rcases p43411_3 (m.d 0 1) (by simp) with h43428 | h43428
                · linarith only [h43428, hlam, p43411_0]
                · rcases p43411_3 (m.d 1 2) (by simp) with h43430 | h43430
                  · rcases p43411_3 (m.d 1 3) (by simp) with h43431 | h43431
                    · rcases p43411_3 (m.d 1 4) (by simp) with h43432 | h43432
                      · linarith only [h43125, h43432, hlam]
                      · linarith only [h36828, h43432, hlam]
                    · linarith only [h43431, hlam, p43411_0]
                  · linarith only [h0, h43430, hlam]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h43122, hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h41031, h41032, h43127, h43128, h43129, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43411_1]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h41031, h41032, h43122, h43127, h43128, h43129, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43411_1]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                rcases p43411_3 (m.d 0 1) (by simp) with h43441 | h43441
                · linarith only [h43441, hlam, p43411_0]
                · rcases p43411_3 (m.d 1 2) (by simp) with h43443 | h43443
                  · rcases p43411_3 (m.d 1 3) (by simp) with h43444 | h43444
                    · rcases p43411_3 (m.d 1 4) (by simp) with h43445 | h43445
                      · rcases p43411_3 (m.d 1 5) (by simp) with h43446 | h43446
                        · linarith only [h43127, h43446, hlam]
                        · linarith only [h39227, h43446, hlam]
                      · linarith only [h43445, hlam, p43411_0]
                    · linarith only [h33187, h43444, hlam]
                  · linarith only [h0, h43443, hlam]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h43123, hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h43125, hlam, p43411_1]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h41031, h41032, h43127, h43128, h43129, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43411_1]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                rcases p43411_3 (m.d 0 1) (by simp) with h43456 | h43456
                · linarith only [h43456, hlam, p43411_0]
                · rcases p43411_3 (m.d 1 2) (by simp) with h43458 | h43458
                  · rcases p43411_3 (m.d 1 3) (by simp) with h43459 | h43459
                    · rcases p43411_3 (m.d 1 4) (by simp) with h43460 | h43460
                      · rcases p43411_3 (m.d 1 5) (by simp) with h43461 | h43461
                        · rcases h1emax with h43462 | h43462 | h43462 | h43462 | h43462
                          · rcases h2bigk with h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c | h43463c
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [h0, hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              rcases p43463_3 (m.d 0 2) (by simp) with h43466 | h43466
                              · rcases p43463_3 (m.d 1 2) (by simp) with h43467 | h43467
                                · rcases p43463_3 (m.d 2 3) (by simp) with h43468 | h43468
                                  · linarith only [h43468, hlam, p43463_0]
                                  · rcases p43463_3 (m.d 2 4) (by simp) with h43470 | h43470
                                    · linarith only [h41028, h43470, hlam]
                                    · rcases p43463_3 (m.d 2 5) (by simp) with h43472 | h43472
                                      · linarith only [h41029, h43472, hlam]
                                      · linarith only [h43129, h43472, hlam]
                                · linarith only [h43122, h43467, hlam]
                              · linarith only [h43466, hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              rcases p43463_3 (m.d 0 2) (by simp) with h43477 | h43477
                              · rcases p43463_3 (m.d 1 2) (by simp) with h43478 | h43478
                                · rcases p43463_3 (m.d 2 3) (by simp) with h43479 | h43479
                                  · linarith only [h41027, h43479, hlam]
                                  · linarith only [h43128, h43479, hlam]
                                · linarith only [h43123, h43478, hlam]
                              · linarith only [h43477, hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              rcases p43463_3 (m.d 0 2) (by simp) with h43484 | h43484
                              · rcases p43463_3 (m.d 1 2) (by simp) with h43485 | h43485
                                · rcases p43463_3 (m.d 2 3) (by simp) with h43486 | h43486
                                  · linarith only [h41027, h43486, hlam]
                                  · rcases p43463_3 (m.d 2 4) (by simp) with h43488 | h43488
                                    · linarith only [h41028, h43488, hlam]
                                    · rcases p43463_3 (m.d 2 5) (by simp) with h43490 | h43490
                                      · linarith only [h43490, hlam, p43463_0]
                                      · rcases h4bigk with h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c | h43492c
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [hlam, p43492_0]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h36828, hlam, p43492_1]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h41032, hc24, hc45, hlam, hphi, p43492_1]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h41032, hc34, hc45, hlam, hphi, p43492_1]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h41032, hlam, p43492_0]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          rcases p43492_3 (m.d 0 4) (by simp) with h43498 | h43498
                                          · linarith only [h36828, h43498, hlam]
                                          · rcases p43492_3 (m.d 1 4) (by simp) with h43500 | h43500
                                            · rcases p43492_3 (m.d 2 4) (by simp) with h43501 | h43501
                                              · linarith only [h43123, h43501, hlam]
                                              · rcases p43492_3 (m.d 3 4) (by simp) with h43503 | h43503
                                                · linarith only [h43125, h43503, hlam]
                                                · rcases p43492_3 (m.d 4 5) (by simp) with h43505 | h43505
                                                  · linarith only [h43127, h43505, hlam]
                                                  · linarith only [h41032, h43505, hlam]
                                            · linarith only [h36828, h43500, hlam]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [hlam, p43492_0]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          rcases p43492_3 (m.d 0 4) (by simp) with h43510 | h43510
                                          · linarith only [h36828, h43510, hlam]
                                          · linarith only [h41028, h43510, hlam]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h41031, h41032, h43127, h43128, h43129, hlam, p43492_2]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h36828, h41032, hc01, hc14, hlam, hphi, p43492_1]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h41028, hlam, p43492_0]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h43123, hlam, p43492_0]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [hlam, p43492_0]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h41028, h41032, hc34, hc45, hlam, hphi, p43492_1]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h43407, hlam, p43492_0]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h41030, hlam, p43492_0]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h43125, hlam, p43492_0]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h43128, hlam, p43492_0]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [hlam, p43492_0]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h43409, hlam, p43492_0]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h36828, h43122, h43125, h43127, hc01, hc12, hlam, hphi, p43492_1]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [h43127, hlam, p43492_0]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          rcases p43492_3 (m.d 0 4) (by simp) with h43527 | h43527
                                          · linarith only [h41032, h43527, hlam]
                                          · linarith only [h41028, h43527, hlam]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          rcases p43492_3 (m.d 0 4) (by simp) with h43530 | h43530
                                          · linarith only [h41032, h43530, hlam]
                                          · linarith only [h41030, h43530, hlam]
                                        · have p43492_0 := h43492c.1
                                          have p43492_1 := h43492c.2.1
                                          have p43492_2 := h43492c.2.2.1
                                          have p43492_3 := h43492c.2.2.2
                                          linarith only [hlam, p43492_0]
                                · linarith only [h43124, h43485, hlam]
                              · linarith only [h43484, hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [h41027, h43128, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43463_1]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              rcases p43463_3 (m.d 0 2) (by simp) with h43538 | h43538
                              · linarith only [h0, h43538, hlam]
                              · linarith only [h41027, h43538, hlam]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              rcases p43463_3 (m.d 0 2) (by simp) with h43541 | h43541
                              · linarith only [h0, h43541, hlam]
                              · linarith only [h41028, h43541, hlam]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              rcases p43463_3 (m.d 0 2) (by simp) with h43544 | h43544
                              · linarith only [h0, h43544, hlam]
                              · linarith only [h41029, h43544, hlam]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [h41027, hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [h43122, hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [h41027, h41031, h43129, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p43463_1]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [h43129, hlam, p43463_1]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [h41028, hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [h43123, hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [h43128, hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [h43407, hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [h41029, hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [h43124, hlam, p43463_0]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [h41029, h41032, h43122, h43125, h43127, h43128, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43463_1]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              rcases p43463_3 (m.d 0 2) (by simp) with h43560 | h43560
                              · rcases p43463_3 (m.d 1 2) (by simp) with h43561 | h43561
                                · rcases p43463_3 (m.d 2 3) (by simp) with h43562 | h43562
                                  · linarith only [h43129, h43562, hlam]
                                  · linarith only [h43128, h43562, hlam]
                                · linarith only [h43123, h43561, hlam]
                              · linarith only [h41028, h43560, hlam]
                            · have p43463_0 := h43463c.1
                              have p43463_1 := h43463c.2.1
                              have p43463_2 := h43463c.2.2.1
                              have p43463_3 := h43463c.2.2.2
                              linarith only [hlam, p43463_0]
                          · linarith only [h0, h43462, hc01, hlam]
                          · linarith only [h41031, h41032, h43125, h43127, h43128, h43129, h43462, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h41031, h41032, h43127, h43128, h43129, h43462, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h43462, hc01, hlam, p43411_1]
                        · linarith only [h43461, hlam, p43411_0]
                      · linarith only [h36828, h43460, hlam]
                    · linarith only [h33187, h43459, hlam]
                  · linarith only [h0, h43458, hlam]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h43124, hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h43126, hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [h43127, hlam, p43411_0]
              · have p43411_0 := h43411c.1
                have p43411_1 := h43411c.2.1
                have p43411_2 := h43411c.2.2.1
                have p43411_3 := h43411c.2.2.2
                linarith only [hlam, p43411_0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h43580 | h43580
        · linarith only [h41030, h41032, h43127, h43128, h43580, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h43582 | h43582
          · linarith only [h41028, h41030, h41032, h43128, h43582, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h43584 | h43584
            · linarith only [h41030, h41032, h43584, hlam]
            · rcases h1bigk with h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c | h43586c
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h0, hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h33187, hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h36828, hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h39227, hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                rcases p43586_3 (m.d 0 1) (by simp) with h43592 | h43592
                · linarith only [h43592, hlam, p43586_0]
                · rcases p43586_3 (m.d 1 2) (by simp) with h43594 | h43594
                  · rcases p43586_3 (m.d 1 3) (by simp) with h43595 | h43595
                    · linarith only [h43122, h43595, hlam]
                    · linarith only [h33187, h43595, hlam]
                  · linarith only [h43594, hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h41030, h41032, h43125, h43127, h43128, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43586_1]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h41030, h41032, h43127, h43128, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43586_1]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h39227, hc01, hc12, hlam, hphi, p43586_1]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                rcases p43586_3 (m.d 0 1) (by simp) with h43603 | h43603
                · linarith only [h43603, hlam, p43586_0]
                · rcases p43586_3 (m.d 1 2) (by simp) with h43605 | h43605
                  · rcases p43586_3 (m.d 1 3) (by simp) with h43606 | h43606
                    · rcases p43586_3 (m.d 1 4) (by simp) with h43607 | h43607
                      · linarith only [h43125, h43607, hlam]
                      · linarith only [h36828, h43607, hlam]
                    · linarith only [h43606, hlam, p43586_0]
                  · linarith only [h0, h43605, hlam]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h43122, hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h41030, h41032, h43127, h43128, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43586_1]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h41030, h41032, h43122, h43127, h43128, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43586_1]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                rcases p43586_3 (m.d 0 1) (by simp) with h43616 | h43616
                · linarith only [h43616, hlam, p43586_0]
                · rcases p43586_3 (m.d 1 2) (by simp) with h43618 | h43618
                  · rcases p43586_3 (m.d 1 3) (by simp) with h43619 | h43619
                    · rcases p43586_3 (m.d 1 4) (by simp) with h43620 | h43620
                      · rcases p43586_3 (m.d 1 5) (by simp) with h43621 | h43621
                        · linarith only [h43127, h43621, hlam]
                        · linarith only [h39227, h43621, hlam]
                      · linarith only [h43620, hlam, p43586_0]
                    · linarith only [h33187, h43619, hlam]
                  · linarith only [h0, h43618, hlam]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h43123, hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h43125, hlam, p43586_1]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h41030, h41032, h43127, h43128, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43586_1]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                rcases p43586_3 (m.d 0 1) (by simp) with h43631 | h43631
                · linarith only [h43631, hlam, p43586_0]
                · rcases p43586_3 (m.d 1 2) (by simp) with h43633 | h43633
                  · rcases p43586_3 (m.d 1 3) (by simp) with h43634 | h43634
                    · rcases p43586_3 (m.d 1 4) (by simp) with h43635 | h43635
                      · rcases p43586_3 (m.d 1 5) (by simp) with h43636 | h43636
                        · rcases h1emax with h43637 | h43637 | h43637 | h43637 | h43637
                          · rcases h2bigk with h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c | h43638c
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [h0, hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              rcases p43638_3 (m.d 0 2) (by simp) with h43641 | h43641
                              · rcases p43638_3 (m.d 1 2) (by simp) with h43642 | h43642
                                · rcases p43638_3 (m.d 2 3) (by simp) with h43643 | h43643
                                  · linarith only [h43643, hlam, p43638_0]
                                  · rcases p43638_3 (m.d 2 4) (by simp) with h43645 | h43645
                                    · linarith only [h41028, h43645, hlam]
                                    · linarith only [h43128, h43645, hlam]
                                · linarith only [h43122, h43642, hlam]
                              · linarith only [h43641, hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              rcases p43638_3 (m.d 0 2) (by simp) with h43650 | h43650
                              · rcases p43638_3 (m.d 1 2) (by simp) with h43651 | h43651
                                · rcases p43638_3 (m.d 2 3) (by simp) with h43652 | h43652
                                  · linarith only [h41027, h43652, hlam]
                                  · rcases p43638_3 (m.d 2 4) (by simp) with h43654 | h43654
                                    · linarith only [h43654, hlam, p43638_0]
                                    · rcases p43638_3 (m.d 2 5) (by simp) with h43656 | h43656
                                      · linarith only [h41029, h43656, hlam]
                                      · linarith only [h43582, h43656, hlam]
                                · linarith only [h43123, h43651, hlam]
                              · linarith only [h43650, hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              rcases p43638_3 (m.d 0 2) (by simp) with h43661 | h43661
                              · rcases p43638_3 (m.d 1 2) (by simp) with h43662 | h43662
                                · rcases p43638_3 (m.d 2 3) (by simp) with h43663 | h43663
                                  · linarith only [h41027, h43663, hlam]
                                  · rcases p43638_3 (m.d 2 4) (by simp) with h43665 | h43665
                                    · linarith only [h41028, h43665, hlam]
                                    · rcases p43638_3 (m.d 2 5) (by simp) with h43667 | h43667
                                      · linarith only [h43667, hlam, p43638_0]
                                      · rcases h4bigk with h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c | h43669c
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [hlam, p43669_0]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h36828, hlam, p43669_1]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h41032, hc24, hc45, hlam, hphi, p43669_1]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h41032, h43128, hc23, hc45, hlam, hphi, ht34, p43669_1]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h41032, hlam, p43669_0]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          rcases p43669_3 (m.d 0 4) (by simp) with h43675 | h43675
                                          · linarith only [h36828, h43675, hlam]
                                          · rcases p43669_3 (m.d 1 4) (by simp) with h43677 | h43677
                                            · rcases p43669_3 (m.d 2 4) (by simp) with h43678 | h43678
                                              · linarith only [h43123, h43678, hlam]
                                              · rcases p43669_3 (m.d 3 4) (by simp) with h43680 | h43680
                                                · linarith only [h43125, h43680, hlam]
                                                · rcases p43669_3 (m.d 4 5) (by simp) with h43682 | h43682
                                                  · linarith only [h43127, h43682, hlam]
                                                  · linarith only [h41032, h43682, hlam]
                                            · linarith only [h36828, h43677, hlam]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [hlam, p43669_0]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          rcases p43669_3 (m.d 0 4) (by simp) with h43687 | h43687
                                          · linarith only [h36828, h43687, hlam]
                                          · linarith only [h41028, h43687, hlam]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          rcases p43669_3 (m.d 0 4) (by simp) with h43690 | h43690
                                          · linarith only [h36828, h43690, hlam]
                                          · linarith only [h41030, h43690, hlam]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h36828, h41032, h43122, h43125, hc01, hc12, hlam, hphi, p43669_1]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h41028, hlam, p43669_0]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h43123, hlam, p43669_0]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [hlam, p43669_0]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h43128, hlam, p43669_1]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h43582, hlam, p43669_0]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h41030, hlam, p43669_0]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h43125, hlam, p43669_0]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h41030, h41032, hc24, hc45, hlam, hphi, p43669_1]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [hlam, p43669_0]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h43584, hlam, p43669_0]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h41030, h43128, hc23, hc45, hlam, hphi, ht34, p43669_1]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h43127, hlam, p43669_0]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          rcases p43669_3 (m.d 0 4) (by simp) with h43706 | h43706
                                          · linarith only [h41032, h43706, hlam]
                                          · linarith only [h41028, h43706, hlam]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [h43122, h43125, h43127, h43128, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43669_1]
                                        · have p43669_0 := h43669c.1
                                          have p43669_1 := h43669c.2.1
                                          have p43669_2 := h43669c.2.2.1
                                          have p43669_3 := h43669c.2.2.2
                                          linarith only [hlam, p43669_0]
                                · linarith only [h43124, h43662, hlam]
                              · linarith only [h43661, hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [h41027, h41031, h43128, h43584, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43638_1]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [h41030, h41032, h43122, h43125, h43127, h43128, hlam, p43638_2]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              rcases p43638_3 (m.d 0 2) (by simp) with h43716 | h43716
                              · linarith only [h0, h43716, hlam]
                              · linarith only [h41028, h43716, hlam]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              rcases p43638_3 (m.d 0 2) (by simp) with h43719 | h43719
                              · linarith only [h0, h43719, hlam]
                              · linarith only [h41029, h43719, hlam]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [h41027, hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [h43122, hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [h43128, hlam, p43638_1]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [h43580, hlam, p43638_1]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [h41028, hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [h43123, hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [h41028, h41032, h43122, h43125, h43127, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43638_1]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [h43582, hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [h41029, hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [h43124, hlam, p43638_0]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              rcases p43638_3 (m.d 0 2) (by simp) with h43734 | h43734
                              · rcases p43638_3 (m.d 1 2) (by simp) with h43735 | h43735
                                · rcases p43638_3 (m.d 2 3) (by simp) with h43736 | h43736
                                  · linarith only [h43580, h43736, hlam]
                                  · rcases p43638_3 (m.d 2 4) (by simp) with h43738 | h43738
                                    · linarith only [h43582, h43738, hlam]
                                    · linarith only [h43128, h43738, hlam]
                                · linarith only [h43122, h43735, hlam]
                              · linarith only [h41027, h43734, hlam]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              rcases p43638_3 (m.d 0 2) (by simp) with h43743 | h43743
                              · rcases p43638_3 (m.d 1 2) (by simp) with h43744 | h43744
                                · rcases p43638_3 (m.d 2 3) (by simp) with h43745 | h43745
                                  · linarith only [h43580, h43745, hlam]
                                  · rcases p43638_3 (m.d 2 4) (by simp) with h43747 | h43747
                                    · linarith only [h43582, h43747, hlam]
                                    · rcases p43638_3 (m.d 2 5) (by simp) with h43749 | h43749
                                      · rcases h4bigk with h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c | h43750c
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [hlam, p43750_0]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h36828, hlam, p43750_1]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h41032, h43122, h43125, h43127, h43128, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43750_1]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h41032, h43122, h43125, h43127, h43128, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43750_1]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h41032, hlam, p43750_0]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          rcases p43750_3 (m.d 0 4) (by simp) with h43756 | h43756
                                          · linarith only [h36828, h43756, hlam]
                                          · rcases p43750_3 (m.d 1 4) (by simp) with h43758 | h43758
                                            · rcases p43750_3 (m.d 2 4) (by simp) with h43759 | h43759
                                              · linarith only [h43123, h43759, hlam]
                                              · rcases p43750_3 (m.d 3 4) (by simp) with h43761 | h43761
                                                · linarith only [h43125, h43761, hlam]
                                                · rcases p43750_3 (m.d 4 5) (by simp) with h43763 | h43763
                                                  · linarith only [h43127, h43763, hlam]
                                                  · linarith only [h41032, h43763, hlam]
                                            · linarith only [h36828, h43758, hlam]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [hlam, p43750_0]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h41031, h41032, h43127, h43580, hlam, p43638_1, p43750_2]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          rcases p43750_3 (m.d 0 4) (by simp) with h43769 | h43769
                                          · linarith only [h36828, h43769, hlam]
                                          · linarith only [h41030, h43769, hlam]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h41031, h41032, h43128, h43580, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43638_1, p43750_1]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h41028, hlam, p43750_0]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h43123, hlam, p43750_0]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [hlam, p43750_0]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h43128, hlam, p43750_1]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h43582, hlam, p43750_0]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h41030, hlam, p43750_0]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h43125, hlam, p43750_0]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h41030, h41032, h43128, hc23, hc45, hlam, hphi, ht34, p43750_1]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [hlam, p43750_0]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h43584, hlam, p43750_0]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h36828, h43122, h43125, h43127, hc01, hc12, hlam, hphi, p43750_1]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h43127, hlam, p43750_0]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          rcases p43750_3 (m.d 0 4) (by simp) with h43785 | h43785
                                          · linarith only [h41032, h43785, hlam]
                                          · linarith only [h41028, h43785, hlam]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [h43122, h43125, h43127, h43128, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43750_1]
                                        · have p43750_0 := h43750c.1
                                          have p43750_1 := h43750c.2.1
                                          have p43750_2 := h43750c.2.2.1
                                          have p43750_3 := h43750c.2.2.2
                                          linarith only [hlam, p43750_0]
                                      · linarith only [h43582, h43749, hlam]
                                · linarith only [h43123, h43744, hlam]
                              · linarith only [h41028, h43743, hlam]
                            · have p43638_0 := h43638c.1
                              have p43638_1 := h43638c.2.1
                              have p43638_2 := h43638c.2.2.1
                              have p43638_3 := h43638c.2.2.2
                              linarith only [hlam, p43638_0]
                          · linarith only [h0, h43637, hc01, hlam]
                          · linarith only [h33187, h43637, hc01, hlam]
                          · linarith only [h41030, h41032, h43127, h43128, h43637, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h43637, hc01, hlam, p43586_1]
                        · linarith only [h43636, hlam, p43586_0]
                      · linarith only [h36828, h43635, hlam]
                    · linarith only [h33187, h43634, hlam]
                  · linarith only [h0, h43633, hlam]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h43124, hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h43126, hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [h43127, hlam, p43586_0]
              · have p43586_0 := h43586c.1
                have p43586_1 := h43586c.2.1
                have p43586_2 := h43586c.2.2.1
                have p43586_3 := h43586c.2.2.2
                linarith only [hlam, p43586_0]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h43806 | h43806
      · rcases m.htr 2 3 5 (by decide) (by decide) with h43807 | h43807
        · rcases m.htr 2 4 5 (by decide) (by decide) with h43808 | h43808
          · linarith only [h36828, h43127, h43808, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h43810 | h43810
            · linarith only [h36828, h41027, h43127, h43806, h43810, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
            · rcases h1bigk with h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c | h43812c
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [hlam, p43812_0]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h0, hlam, p43812_0]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h33187, hlam, p43812_0]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h36828, hlam, p43812_0]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h39227, hlam, p43812_0]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                rcases p43812_3 (m.d 0 1) (by simp) with h43818 | h43818
                · linarith only [h43818, hlam, p43812_0]
                · rcases p43812_3 (m.d 1 2) (by simp) with h43820 | h43820
                  · rcases p43812_3 (m.d 1 3) (by simp) with h43821 | h43821
                    · linarith only [h43122, h43821, hlam]
                    · linarith only [h33187, h43821, hlam]
                  · linarith only [h43820, hlam, p43812_0]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [hlam, p43812_0]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h33187, hc01, hc12, hlam, hphi, p43812_1]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h36828, hc01, hc12, hlam, hphi, p43812_1]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h36828, h43127, hc01, hc12, hlam, hphi, p43812_1]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                rcases p43812_3 (m.d 0 1) (by simp) with h43829 | h43829
                · linarith only [h43829, hlam, p43812_0]
                · rcases p43812_3 (m.d 1 2) (by simp) with h43831 | h43831
                  · rcases p43812_3 (m.d 1 3) (by simp) with h43832 | h43832
                    · rcases p43812_3 (m.d 1 4) (by simp) with h43833 | h43833
                      · linarith only [h43125, h43833, hlam]
                      · linarith only [h36828, h43833, hlam]
                    · linarith only [h43832, hlam, p43812_0]
                  · linarith only [h0, h43831, hlam]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h43122, hlam, p43812_0]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [hlam, p43812_0]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h36828, hc01, hc13, hlam, hphi, p43812_1]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h36828, h43122, h43127, hc01, hc12, hlam, hphi, p43812_1]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h43127, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p43812_1]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h43123, hlam, p43812_0]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h43125, hlam, p43812_1]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [hlam, p43812_0]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h43127, hlam, p43812_1]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                rcases p43812_3 (m.d 0 1) (by simp) with h43847 | h43847
                · linarith only [h43847, hlam, p43812_0]
                · rcases p43812_3 (m.d 1 2) (by simp) with h43849 | h43849
                  · rcases p43812_3 (m.d 1 3) (by simp) with h43850 | h43850
                    · rcases p43812_3 (m.d 1 4) (by simp) with h43851 | h43851
                      · linarith only [h43127, h43851, hlam]
                      · linarith only [h36828, h43851, hlam]
                    · linarith only [h33187, h43850, hlam]
                  · linarith only [h0, h43849, hlam]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h43124, hlam, p43812_0]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h43126, hlam, p43812_0]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [h36828, hc01, hc15, hlam, hphi, p43812_1]
              · have p43812_0 := h43812c.1
                have p43812_1 := h43812c.2.1
                have p43812_2 := h43812c.2.2.1
                have p43812_3 := h43812c.2.2.2
                linarith only [hlam, p43812_0]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h43860 | h43860
          · linarith only [h0, h39227, h41028, h43127, h43860, hc01, hc12, hlam, hphi]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h43862 | h43862
            · linarith only [h36828, h41031, h43127, h43806, h43807, h43862, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
            · rcases h1bigk with h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c | h43864c
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [hlam, p43864_0]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h0, hlam, p43864_0]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h33187, hlam, p43864_0]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h36828, hlam, p43864_0]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h39227, hlam, p43864_0]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                rcases p43864_3 (m.d 0 1) (by simp) with h43870 | h43870
                · linarith only [h43870, hlam, p43864_0]
                · rcases p43864_3 (m.d 1 2) (by simp) with h43872 | h43872
                  · rcases p43864_3 (m.d 1 3) (by simp) with h43873 | h43873
                    · linarith only [h43122, h43873, hlam]
                    · linarith only [h33187, h43873, hlam]
                  · linarith only [h43872, hlam, p43864_0]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [hlam, p43864_0]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h33187, hc01, hc12, hlam, hphi, p43864_1]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h36828, hc01, hc12, hlam, hphi, p43864_1]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h39227, hc01, hc12, hlam, hphi, p43864_1]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                rcases p43864_3 (m.d 0 1) (by simp) with h43881 | h43881
                · linarith only [h43881, hlam, p43864_0]
                · rcases p43864_3 (m.d 1 2) (by simp) with h43883 | h43883
                  · rcases p43864_3 (m.d 1 3) (by simp) with h43884 | h43884
                    · rcases p43864_3 (m.d 1 4) (by simp) with h43885 | h43885
                      · linarith only [h43125, h43885, hlam]
                      · linarith only [h36828, h43885, hlam]
                    · linarith only [h43884, hlam, p43864_0]
                  · linarith only [h0, h43883, hlam]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h43122, hlam, p43864_0]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [hlam, p43864_0]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h36828, hc01, hc13, hlam, hphi, p43864_1]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h39227, h41031, h43122, h43806, h43807, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43864_1]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h43127, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p43864_1]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h43123, hlam, p43864_0]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h43125, hlam, p43864_1]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [hlam, p43864_0]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h43127, hlam, p43864_1]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                rcases p43864_3 (m.d 0 1) (by simp) with h43899 | h43899
                · linarith only [h43899, hlam, p43864_0]
                · rcases p43864_3 (m.d 1 2) (by simp) with h43901 | h43901
                  · rcases p43864_3 (m.d 1 3) (by simp) with h43902 | h43902
                    · rcases p43864_3 (m.d 1 4) (by simp) with h43903 | h43903
                      · linarith only [h43127, h43903, hlam]
                      · linarith only [h36828, h43903, hlam]
                    · linarith only [h33187, h43902, hlam]
                  · linarith only [h0, h43901, hlam]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h43124, hlam, p43864_0]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h43126, hlam, p43864_0]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [h36828, hc01, hc15, hlam, hphi, p43864_1]
              · have p43864_0 := h43864c.1
                have p43864_1 := h43864c.2.1
                have p43864_2 := h43864c.2.2.1
                have p43864_3 := h43864c.2.2.2
                linarith only [hlam, p43864_0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h43912 | h43912
        · rcases m.htr 2 4 5 (by decide) (by decide) with h43913 | h43913
          · linarith only [h39227, h41030, h41032, h43127, h43806, h43913, hlam]
          · linarith only [h43806, h43912, h43913, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h43916 | h43916
          · linarith only [h36828, h43127, h43916, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h43918 | h43918
            · linarith only [h36828, h41030, h43127, h43918, hlam]
            · rcases h1bigk with h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c | h43920c
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [hlam, p43920_0]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h0, hlam, p43920_0]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h33187, hlam, p43920_0]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h36828, hlam, p43920_0]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h39227, hlam, p43920_0]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                rcases p43920_3 (m.d 0 1) (by simp) with h43926 | h43926
                · linarith only [h43926, hlam, p43920_0]
                · rcases p43920_3 (m.d 1 2) (by simp) with h43928 | h43928
                  · rcases p43920_3 (m.d 1 3) (by simp) with h43929 | h43929
                    · linarith only [h43122, h43929, hlam]
                    · linarith only [h33187, h43929, hlam]
                  · linarith only [h43928, hlam, p43920_0]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [hlam, p43920_0]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h33187, hc01, hc12, hlam, hphi, p43920_1]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h36828, hc01, hc12, hlam, hphi, p43920_1]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h39227, hc01, hc12, hlam, hphi, p43920_1]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                rcases p43920_3 (m.d 0 1) (by simp) with h43937 | h43937
                · linarith only [h43937, hlam, p43920_0]
                · rcases p43920_3 (m.d 1 2) (by simp) with h43939 | h43939
                  · rcases p43920_3 (m.d 1 3) (by simp) with h43940 | h43940
                    · rcases p43920_3 (m.d 1 4) (by simp) with h43941 | h43941
                      · linarith only [h43125, h43941, hlam]
                      · linarith only [h36828, h43941, hlam]
                    · linarith only [h43940, hlam, p43920_0]
                  · linarith only [h0, h43939, hlam]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h43122, hlam, p43920_0]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [hlam, p43920_0]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h36828, hc01, hc13, hlam, hphi, p43920_1]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h36828, h43122, h43127, hc01, hc12, hlam, hphi, p43920_1]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h43127, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p43920_1]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h43123, hlam, p43920_0]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h43125, hlam, p43920_1]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [hlam, p43920_0]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h43127, hlam, p43920_1]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                rcases p43920_3 (m.d 0 1) (by simp) with h43955 | h43955
                · linarith only [h43955, hlam, p43920_0]
                · rcases p43920_3 (m.d 1 2) (by simp) with h43957 | h43957
                  · rcases p43920_3 (m.d 1 3) (by simp) with h43958 | h43958
                    · rcases p43920_3 (m.d 1 4) (by simp) with h43959 | h43959
                      · linarith only [h43127, h43959, hlam]
                      · linarith only [h36828, h43959, hlam]
                    · linarith only [h33187, h43958, hlam]
                  · linarith only [h0, h43957, hlam]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h43124, hlam, p43920_0]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h43126, hlam, p43920_0]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [h36828, hc01, hc15, hlam, hphi, p43920_1]
              · have p43920_0 := h43920c.1
                have p43920_1 := h43920c.2.1
                have p43920_2 := h43920c.2.2.1
                have p43920_3 := h43920c.2.2.2
                linarith only [hlam, p43920_0]
  · linarith only [h33187, h41031, h43126, hlam]

end R2N4
