import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S49
import Jsp000404.R1LeavesN7_1S51

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 22740000 in
set_option maxHeartbeats 22740000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h20697 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h20698 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  rcases m.htr 0 2 4 (by decide) (by decide) with h21942 | h21942
  · rcases m.htr 0 2 5 (by decide) (by decide) with h21943 | h21943
    · rcases m.htr 0 3 4 (by decide) (by decide) with h21944 | h21944
      · rcases m.htr 0 3 5 (by decide) (by decide) with h21945 | h21945
        · rcases m.htr 0 4 5 (by decide) (by decide) with h21946 | h21946
          · rcases m.htr 1 2 3 (by decide) (by decide) with h21947 | h21947
            · rcases m.htr 1 2 4 (by decide) (by decide) with h21948 | h21948
              · rcases m.htr 1 2 5 (by decide) (by decide) with h21949 | h21949
                · rcases m.htr 1 3 4 (by decide) (by decide) with h21950 | h21950
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h21951 | h21951
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h21952 | h21952
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h21953 | h21953
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h21954 | h21954
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h21955 | h21955
                            · linarith only [h20698, h21942, h21947, h21955, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h20698, h21942, h21946, h21947, h21955, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h15532, h18443, h20698, h21942, h21945, h21947, h21954, hc01, hc12, hlam, hphi]
                        · linarith only [h20698, h21944, h21953, hlam]
                      · linarith only [h18443, h20697, h21946, h21949, h21952, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h15532, h20697, h21945, h21949, h21951, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h15532, h20697, h20698, h21942, h21944, h21947, h21949, h21950, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h20698, h21947, h21949, hc02, hc25, hlam, hphi]
              · linarith only [h20698, h21942, h21947, h21948, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h21965 | h21965
              · rcases m.htr 1 2 5 (by decide) (by decide) with h21966 | h21966
                · rcases m.htr 1 3 4 (by decide) (by decide) with h21967 | h21967
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h21968 | h21968
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h21969 | h21969
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h21970 | h21970
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h21971 | h21971
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h21972 | h21972
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h21973 | h21973
                              · rcases h0bigk with h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c | h21974c
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [hlam, p21974_0]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h0, hlam, p21974_1]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h15532, hlam, p21974_0]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h18443, hlam, p21974_1]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h18443, h21947, h21965, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p21974_1]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h0, h21947, hc01, hc23, hlam, hphi, ht12, p21974_1]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [hlam, p21974_0]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h20698, hlam, p21974_0]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h0, h18443, h20697, h21947, h21966, h21971, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p21974_1]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  rcases p21974_3 (m.d 0 1) (by simp) with h21984 | h21984
                                  · linarith only [h0, h21984, hlam]
                                  · linarith only [h20697, h21984, hlam]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  rcases p21974_3 (m.d 0 1) (by simp) with h21987 | h21987
                                  · linarith only [h15532, h21987, hlam]
                                  · rcases p21974_3 (m.d 0 2) (by simp) with h21989 | h21989
                                    · linarith only [h20698, h21989, hlam]
                                    · linarith only [h0, h21989, hlam]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h15532, h21942, h21947, h21970, h21973, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p21974_1]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [hlam, p21974_0]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  rcases p21974_3 (m.d 0 1) (by simp) with h21994 | h21994
                                  · linarith only [h15532, h21994, hlam]
                                  · rcases p21974_3 (m.d 0 2) (by simp) with h21996 | h21996
                                    · linarith only [h20698, h21996, hlam]
                                    · linarith only [h21942, h21996, hlam]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  rcases p21974_3 (m.d 0 1) (by simp) with h21999 | h21999
                                  · linarith only [h15532, h21999, hlam]
                                  · linarith only [h20697, h21999, hlam]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h18443, h20697, h21947, h21965, h21966, h21971, h21973, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p21974_1]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h21942, hlam, p21974_0]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h21944, hlam, p21974_0]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [hlam, p21974_0]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  rcases p21974_3 (m.d 0 1) (by simp) with h22006 | h22006
                                  · linarith only [h18443, h22006, hlam]
                                  · linarith only [h20697, h22006, hlam]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h20697, hlam, p21974_0]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h21943, hlam, p21974_1]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h21945, hlam, p21974_0]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [h21946, hlam, p21974_1]
                                · have p21974_0 := h21974c.1
                                  have p21974_1 := h21974c.2.1
                                  have p21974_2 := h21974c.2.2.1
                                  have p21974_3 := h21974c.2.2.2
                                  linarith only [hlam, p21974_0]
                              · linarith only [h0, h20697, h21947, h21969, h21973, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h18443, h20697, h21947, h21965, h21969, h21972, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h18443, h21947, h21965, h21971, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h18443, h20697, h21947, h21965, h21969, h21970, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h18443, h21946, h21969, hlam]
                    · linarith only [h15532, h21945, h21968, hlam]
                  · linarith only [h15532, h20698, h21942, h21944, h21967, hlam]
                · linarith only [h0, h21943, h21966, hlam]
              · linarith only [h0, h21942, h21965, hlam]
          · linarith only [h18443, h20697, h21946, hlam]
        · linarith only [h15532, h20697, h21945, hlam]
      · linarith only [h20698, h21942, h21944, hlam]
    · linarith only [h0, h20697, h21943, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h22027 | h22027
    · rcases m.htr 0 3 4 (by decide) (by decide) with h22028 | h22028
      · rcases m.htr 0 3 5 (by decide) (by decide) with h22029 | h22029
        · rcases m.htr 0 4 5 (by decide) (by decide) with h22030 | h22030
          · rcases m.htr 1 2 3 (by decide) (by decide) with h22031 | h22031
            · rcases m.htr 1 2 4 (by decide) (by decide) with h22032 | h22032
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22033 | h22033
                · rcases m.htr 1 3 4 (by decide) (by decide) with h22034 | h22034
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22035 | h22035
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22036 | h22036
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22037 | h22037
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22038 | h22038
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22039 | h22039
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h22040 | h22040
                              · rcases h0bigk with h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c | h22041c
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [hlam, p22041_0]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h0, hlam, p22041_1]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h15532, hlam, p22041_0]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h18443, hlam, p22041_1]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h0, h21942, h22031, h22037, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p22041_1]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h21942, h22031, h22037, hc01, hc12, hlam, hphi, p22041_1]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [hlam, p22041_0]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h20698, hlam, p22041_0]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h21942, hlam, p22041_1]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h20697, h21942, h22031, h22033, h22037, h22038, h22040, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22041_1]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h20697, h20698, h22031, h22033, h22038, h22040, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22041_1]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h0, h20697, h20698, h22031, h22033, h22038, h22040, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22041_1]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [hlam, p22041_0]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h0, h20697, h20698, h21942, h22031, h22033, h22038, h22040, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22041_1]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  rcases p22041_3 (m.d 0 1) (by simp) with h22056 | h22056
                                  · linarith only [h15532, h22056, hlam]
                                  · linarith only [h20697, h22056, hlam]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h20697, h21942, h22031, h22033, h22037, h22038, h22040, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22041_1]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h0, h20697, h21942, h22031, h22033, h22037, h22038, h22040, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22041_1]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h22028, hlam, p22041_0]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [hlam, p22041_0]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  rcases p22041_3 (m.d 0 1) (by simp) with h22063 | h22063
                                  · linarith only [h18443, h22063, hlam]
                                  · linarith only [h20697, h22063, hlam]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h20697, hlam, p22041_0]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h22027, hlam, p22041_1]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h22029, hlam, p22041_0]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [h22030, hlam, p22041_1]
                                · have p22041_0 := h22041c.1
                                  have p22041_1 := h22041c.2.1
                                  have p22041_2 := h22041c.2.2.1
                                  have p22041_3 := h22041c.2.2.2
                                  linarith only [hlam, p22041_0]
                              · linarith only [h0, h20697, h21942, h22031, h22036, h22037, h22040, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h20697, h21942, h22036, h22039, hlam]
                          · linarith only [h20698, h22029, h22038, hlam]
                        · linarith only [h20698, h22028, h22037, hlam]
                      · linarith only [h18443, h20698, h22028, h22030, h22031, h22036, hc01, hc12, hlam, hphi]
                    · linarith only [h15532, h22029, h22035, hlam]
                  · linarith only [h20698, h22028, h22031, h22034, hlam]
                · linarith only [h0, h20697, h22027, h22033, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h20698, h22031, h22032, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h22080 | h22080
              · linarith only [h0, h20697, h21942, h22031, h22080, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22082 | h22082
                · rcases m.htr 1 3 4 (by decide) (by decide) with h22083 | h22083
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22084 | h22084
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22085 | h22085
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22086 | h22086
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22087 | h22087
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22088 | h22088
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h22089 | h22089
                              · rcases h0bigk with h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c | h22090c
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [hlam, p22090_0]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [h0, hlam, p22090_1]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [h15532, hlam, p22090_0]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [h18443, hlam, p22090_1]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [h0, h22080, h22086, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p22090_1]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [h0, h22080, h22086, hc01, hc23, hlam, hphi, ht12, p22090_1]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [hlam, p22090_0]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [h20698, hlam, p22090_0]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [h21942, hlam, p22090_1]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  rcases p22090_3 (m.d 0 1) (by simp) with h22100 | h22100
                                  · linarith only [h0, h22100, hlam]
                                  · linarith only [h20697, h22100, hlam]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  rcases p22090_3 (m.d 0 1) (by simp) with h22103 | h22103
                                  · linarith only [h15532, h22103, hlam]
                                  · rcases p22090_3 (m.d 0 2) (by simp) with h22105 | h22105
                                    · linarith only [h20698, h22105, hlam]
                                    · linarith only [h0, h22105, hlam]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  rcases p22090_3 (m.d 0 1) (by simp) with h22108 | h22108
                                  · linarith only [h15532, h22108, hlam]
                                  · rcases p22090_3 (m.d 0 2) (by simp) with h22110 | h22110
                                    · linarith only [h20698, h22110, hlam]
                                    · rcases p22090_3 (m.d 0 3) (by simp) with h22112 | h22112
                                      · rcases p22090_3 (m.d 0 4) (by simp) with h22113 | h22113
                                        · linarith only [h22028, h22113, hlam]
                                        · linarith only [h21942, h22113, hlam]
                                      · linarith only [h20698, h22112, hlam]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [hlam, p22090_0]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  rcases p22090_3 (m.d 0 1) (by simp) with h22118 | h22118
                                  · linarith only [h15532, h22118, hlam]
                                  · rcases p22090_3 (m.d 0 2) (by simp) with h22120 | h22120
                                    · linarith only [h20698, h22120, hlam]
                                    · rcases p22090_3 (m.d 0 3) (by simp) with h22122 | h22122
                                      · rcases p22090_3 (m.d 0 4) (by simp) with h22123 | h22123
                                        · linarith only [h22028, h22123, hlam]
                                        · rcases p22090_3 (m.d 0 5) (by simp) with h22125 | h22125
                                          · linarith only [h22029, h22125, hlam]
                                          · rcases h2bigk with h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c | h22127c
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [hlam, p22127_0]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h0, hlam, p22127_1]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h20698, hlam, p22127_0]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h21942, hlam, p22127_0]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h21942, h22087, h22089, hc03, hc45, hlam, hphi, ht0b, ht5b, p22090_1, p22127_1]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h22080, h22086, hc02, hc23, hlam, hphi, p22127_1]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [hlam, p22127_0]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h22031, hlam, p22127_0]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h22080, hlam, p22127_0]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              rcases p22127_3 (m.d 0 2) (by simp) with h22137 | h22137
                                              · linarith only [h0, h22137, hlam]
                                              · linarith only [h22027, h22137, hlam]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              rcases p22127_3 (m.d 0 2) (by simp) with h22140 | h22140
                                              · linarith only [h22140, hlam, p22127_0]
                                              · rcases p22127_3 (m.d 1 2) (by simp) with h22142 | h22142
                                                · linarith only [h22031, h22142, hlam]
                                                · linarith only [h0, h22142, hlam]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h0, h20697, h22082, h22087, h22089, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22127_1]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [hlam, p22127_0]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h0, h20697, h21942, h22082, h22087, h22089, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22127_1]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h15532, h18443, h20697, h22031, h22082, hlam, p22090_1, p22127_2]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              rcases p22127_3 (m.d 0 2) (by simp) with h22149 | h22149
                                              · linarith only [h22149, hlam, p22127_0]
                                              · rcases p22127_3 (m.d 1 2) (by simp) with h22151 | h22151
                                                · linarith only [h22080, h22151, hlam]
                                                · linarith only [h0, h22151, hlam]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h0, h20697, h22082, h22087, h22089, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22127_1]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h22086, hlam, p22127_1]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [hlam, p22127_0]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h0, h20697, h22080, h22082, hlam, p22127_2]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h22027, hlam, p22127_0]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h22082, hlam, p22127_0]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h22087, hlam, p22127_1]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [h22088, hlam, p22127_0]
                                            · have p22127_0 := h22127c.1
                                              have p22127_1 := h22127c.2.1
                                              have p22127_2 := h22127c.2.2.1
                                              have p22127_3 := h22127c.2.2.2
                                              linarith only [hlam, p22127_0]
                                      · linarith only [h22028, h22122, hlam]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  rcases p22090_3 (m.d 0 1) (by simp) with h22164 | h22164
                                  · linarith only [h15532, h22164, hlam]
                                  · linarith only [h20697, h22164, hlam]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  rcases p22090_3 (m.d 0 1) (by simp) with h22167 | h22167
                                  · linarith only [h18443, h22167, hlam]
                                  · rcases p22090_3 (m.d 0 2) (by simp) with h22169 | h22169
                                    · linarith only [h21942, h22169, hlam]
                                    · linarith only [h0, h22169, hlam]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  rcases p22090_3 (m.d 0 1) (by simp) with h22172 | h22172
                                  · linarith only [h18443, h22172, hlam]
                                  · rcases p22090_3 (m.d 0 2) (by simp) with h22174 | h22174
                                    · linarith only [h21942, h22174, hlam]
                                    · rcases p22090_3 (m.d 0 3) (by simp) with h22176 | h22176
                                      · rcases p22090_3 (m.d 0 4) (by simp) with h22177 | h22177
                                        · rcases p22090_3 (m.d 0 5) (by simp) with h22178 | h22178
                                          · linarith only [h22030, h22178, hlam]
                                          · rcases h2bigk with h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c | h22180c
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [hlam, p22180_0]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h0, hlam, p22180_1]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h20698, hlam, p22180_0]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h21942, hlam, p22180_0]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h22087, h22089, hc04, hc45, hlam, hphi, ht0b, ht5b, p22090_1, p22180_1]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h22031, hc02, hc23, hlam, hphi, p22180_1]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [hlam, p22180_0]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h22031, hlam, p22180_0]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h22080, hlam, p22180_0]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              rcases p22180_3 (m.d 0 2) (by simp) with h22190 | h22190
                                              · linarith only [h0, h22190, hlam]
                                              · linarith only [h22027, h22190, hlam]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              rcases p22180_3 (m.d 0 2) (by simp) with h22193 | h22193
                                              · linarith only [h22193, hlam, p22180_0]
                                              · rcases p22180_3 (m.d 1 2) (by simp) with h22195 | h22195
                                                · linarith only [h22031, h22195, hlam]
                                                · linarith only [h0, h22195, hlam]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h0, h20697, h22082, h22087, h22089, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22180_1]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [hlam, p22180_0]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h0, h20697, h21942, h22082, h22087, h22089, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22180_1]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h0, h15532, h20697, h22028, h22031, h22082, hlam, p22090_1, p22180_2]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              rcases p22180_3 (m.d 0 2) (by simp) with h22202 | h22202
                                              · linarith only [h22202, hlam, p22180_0]
                                              · rcases p22180_3 (m.d 1 2) (by simp) with h22204 | h22204
                                                · linarith only [h22080, h22204, hlam]
                                                · linarith only [h0, h22204, hlam]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h0, h22086, hc01, hc23, hlam, hphi, ht12, p22180_1]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h22086, hlam, p22180_1]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [hlam, p22180_0]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h0, h20697, h21942, h22082, hlam, p22090_1, p22180_2]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h22027, hlam, p22180_0]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h22082, hlam, p22180_0]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h22087, hlam, p22180_1]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [h22088, hlam, p22180_0]
                                            · have p22180_0 := h22180c.1
                                              have p22180_1 := h22180c.2.1
                                              have p22180_2 := h22180c.2.2.1
                                              have p22180_3 := h22180c.2.2.2
                                              linarith only [hlam, p22180_0]
                                        · linarith only [h21942, h22177, hlam]
                                      · linarith only [h20698, h22176, hlam]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [h22028, hlam, p22090_0]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [hlam, p22090_0]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  rcases p22090_3 (m.d 0 1) (by simp) with h22220 | h22220
                                  · linarith only [h18443, h22220, hlam]
                                  · linarith only [h20697, h22220, hlam]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [h20697, hlam, p22090_0]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [h22027, hlam, p22090_1]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [h22029, hlam, p22090_0]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [h22030, hlam, p22090_1]
                                · have p22090_0 := h22090c.1
                                  have p22090_1 := h22090c.2.1
                                  have p22090_2 := h22090c.2.2.1
                                  have p22090_3 := h22090c.2.2.2
                                  linarith only [hlam, p22090_0]
                              · linarith only [h0, h20697, h22080, h22085, h22089, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h20697, h22080, h22085, h22088, hlam]
                          · linarith only [h0, h22080, h22086, h22087, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h20697, h22031, h22085, h22086, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h18443, h20697, h22028, h22030, h22085, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h15532, h22029, h22084, hlam]
                  · linarith only [h15532, h22028, h22083, hlam]
                · linarith only [h0, h20697, h22027, h22082, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h20697, h21942, h22030, hlam]
        · linarith only [h15532, h20697, h22029, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h22238 | h22238
        · rcases m.htr 0 4 5 (by decide) (by decide) with h22239 | h22239
          · rcases m.htr 1 2 3 (by decide) (by decide) with h22240 | h22240
            · rcases m.htr 1 2 4 (by decide) (by decide) with h22241 | h22241
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22242 | h22242
                · rcases m.htr 1 3 4 (by decide) (by decide) with h22243 | h22243
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22244 | h22244
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22245 | h22245
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22246 | h22246
                        · linarith only [h0, h20697, h20698, h22028, h22240, h22242, h22246, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h20697, h20698, h22242, h22243, h22246, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h18443, h20697, h22239, h22242, h22245, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h22028, h22238, h22244, hc13, hc34, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22251 | h22251
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22252 | h22252
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22253 | h22253
                        · linarith only [h22240, h22243, h22253, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22255 | h22255
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22256 | h22256
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h22257 | h22257
                              · rcases h0bigk with h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c | h22258c
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [hlam, p22258_0]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h0, hlam, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h15532, hlam, p22258_0]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h18443, hlam, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h0, h20698, h22240, h22243, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h20698, h22240, h22243, hc01, hc34, hlam, hphi, ht12, ht23, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [hlam, p22258_0]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h20698, hlam, p22258_0]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h21942, hlam, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h20697, h20698, h22240, h22242, h22243, h22255, h22257, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h20697, h20698, h22240, h22242, h22243, h22255, h22257, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h20698, h22240, h22243, hc02, hc34, hlam, hphi, ht23, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [hlam, p22258_0]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h22028, hlam, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  rcases p22258_3 (m.d 0 1) (by simp) with h22273 | h22273
                                  · linarith only [h15532, h22273, hlam]
                                  · linarith only [h20697, h22273, hlam]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h20697, h21942, h22241, h22242, h22255, h22257, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h0, h20697, h21942, h22241, h22242, h22255, h22257, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h15532, h20697, h21942, h22241, h22242, h22255, h22257, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [hlam, p22258_0]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  rcases p22258_3 (m.d 0 1) (by simp) with h22280 | h22280
                                  · linarith only [h18443, h22280, hlam]
                                  · linarith only [h20697, h22280, hlam]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h20697, hlam, p22258_0]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h22027, hlam, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h22238, hlam, p22258_0]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [h22239, hlam, p22258_1]
                                · have p22258_0 := h22258c.1
                                  have p22258_1 := h22258c.2.1
                                  have p22258_2 := h22258c.2.2.1
                                  have p22258_3 := h22258c.2.2.2
                                  linarith only [hlam, p22258_0]
                              · linarith only [h15532, h22243, h22257, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h0, h20697, h20698, h22252, h22253, h22256, hlam]
                          · linarith only [h0, h20697, h20698, h22238, h22242, h22255, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h20697, h20698, h22239, h22240, h22242, h22243, h22252, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h20697, h20698, h22238, h22240, h22242, h22251, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h18443, h21942, h22027, h22241, h22242, hlam]
              · linarith only [h0, h20698, h22240, h22241, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h22295 | h22295
              · linarith only [h0, h20697, h21942, h22240, h22295, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22297 | h22297
                · rcases m.htr 1 3 4 (by decide) (by decide) with h22298 | h22298
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22299 | h22299
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22300 | h22300
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22301 | h22301
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22302 | h22302
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22303 | h22303
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h22304 | h22304
                              · rcases h0bigk with h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c | h22305c
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [hlam, p22305_0]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h0, hlam, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h15532, hlam, p22305_0]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h18443, hlam, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h0, h20697, h22295, h22297, h22301, h22302, h22304, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h0, h22295, h22301, hc01, hc23, hlam, hphi, ht12, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [hlam, p22305_0]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h20698, hlam, p22305_0]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h21942, hlam, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h20697, h20698, h22028, h22240, h22297, h22298, h22302, h22304, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h20697, h22028, h22240, h22297, h22298, h22302, h22304, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h22028, h22240, h22298, hc02, hc23, hlam, hphi, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [hlam, p22305_0]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h22028, hlam, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h20697, h22028, h22240, h22297, h22298, h22302, h22304, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h20697, h22028, h22240, h22297, h22298, h22302, h22304, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h0, h20697, h22028, h22240, h22297, h22298, h22302, h22304, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h15532, h20697, h22028, h22240, h22297, h22298, h22302, h22304, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [hlam, p22305_0]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  rcases p22305_3 (m.d 0 1) (by simp) with h22325 | h22325
                                  · linarith only [h18443, h22325, hlam]
                                  · linarith only [h20697, h22325, hlam]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h20697, hlam, p22305_0]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h22027, hlam, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h22238, hlam, p22305_0]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [h22239, hlam, p22305_1]
                                · have p22305_0 := h22305c.1
                                  have p22305_1 := h22305c.2.1
                                  have p22305_2 := h22305c.2.2.1
                                  have p22305_3 := h22305c.2.2.2
                                  linarith only [hlam, p22305_0]
                              · linarith only [h0, h20697, h20698, h22028, h22239, h22304, hc04, hc15, hlam, hphi, ht0b, ht5b]
                            · linarith only [h0, h20697, h20698, h22028, h22240, h22295, h22298, h22300, h22303, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h20697, h20698, h22028, h22240, h22297, h22298, h22302, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h22240, h22298, h22301, hlam]
                      · linarith only [h18443, h20697, h22239, h22297, h22300, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h22028, h22238, h22299, hc13, hc34, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22339 | h22339
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22340 | h22340
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22341 | h22341
                        · linarith only [h0, h22240, h22298, h22341, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h20697, h22240, h22297, h22341, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h18443, h22239, h22340, hlam]
                    · linarith only [h0, h20697, h22238, h22240, h22297, h22339, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h20697, h22027, h22297, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h20697, h20698, h22028, h22239, hlam]
        · linarith only [h0, h20697, h20698, h22238, hlam]
    · linarith only [h0, h20697, h22027, hlam]

set_option maxHeartbeats 22740000 in
set_option maxHeartbeats 22740000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h20697 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  rcases m.htr 0 2 3 (by decide) (by decide) with h20698 | h20698
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 h20697 h20698
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 h20697 h20698

set_option maxHeartbeats 22740000 in
set_option maxHeartbeats 22740000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20 m hb0 hb2 hb3 hb5 h0 h15532 h18443 h20697

set_option maxHeartbeats 22740000 in
set_option maxHeartbeats 22740000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  rcases m.htr 0 1 5 (by decide) (by decide) with h20697 | h20697
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 h20697
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 h20697

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 1 2 3 (by decide) (by decide) with h18451 | h18451
  · rcases m.htr 1 2 4 (by decide) (by decide) with h18452 | h18452
    · rcases m.htr 1 2 5 (by decide) (by decide) with h18453 | h18453
      · rcases m.htr 1 3 4 (by decide) (by decide) with h18454 | h18454
        · rcases m.htr 1 3 5 (by decide) (by decide) with h18455 | h18455
          · rcases m.htr 1 4 5 (by decide) (by decide) with h18456 | h18456
            · rcases m.htr 2 3 4 (by decide) (by decide) with h18457 | h18457
              · rcases m.htr 2 3 5 (by decide) (by decide) with h18458 | h18458
                · rcases m.htr 2 4 5 (by decide) (by decide) with h18459 | h18459
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h18460 | h18460
                    · rcases h0bigk with h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c | h18461c
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [hlam, p18461_0]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h0, hlam, p18461_1]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h15532, hlam, p18461_0]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h15532, h18443, h18452, h18457, h18460, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p18461_1]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        rcases p18461_3 (m.d 0 1) (by simp) with h18466 | h18466
                        · rcases p18461_3 (m.d 0 2) (by simp) with h18467 | h18467
                          · rcases p18461_3 (m.d 0 3) (by simp) with h18468 | h18468
                            · rcases p18461_3 (m.d 0 4) (by simp) with h18469 | h18469
                              · linarith only [h18443, h18469, hlam]
                              · linarith only [h18450, h18469, hlam]
                            · linarith only [h18449, h18468, hlam]
                          · linarith only [h18447, h18467, hlam]
                        · linarith only [h18444, h18466, hlam]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h0, h18443, h18452, h18457, h18460, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18461_1]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [hlam, p18461_0]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h0, h15532, h18443, h18452, h18457, h18460, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18461_1]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        rcases p18461_3 (m.d 0 1) (by simp) with h18478 | h18478
                        · linarith only [h0, h18478, hlam]
                        · linarith only [h18443, h18478, hlam]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        rcases p18461_3 (m.d 0 1) (by simp) with h18481 | h18481
                        · linarith only [h0, h18481, hlam]
                        · linarith only [h18444, h18481, hlam]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h18443, h18452, h18457, h18460, hc03, hc45, hlam, hphi, ht0b, ht5b, p18461_1]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h18445, hlam, p18461_1]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [hlam, p18461_0]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        rcases p18461_3 (m.d 0 1) (by simp) with h18487 | h18487
                        · linarith only [h15532, h18487, hlam]
                        · linarith only [h18443, h18487, hlam]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        rcases p18461_3 (m.d 0 1) (by simp) with h18490 | h18490
                        · linarith only [h15532, h18490, hlam]
                        · linarith only [h18444, h18490, hlam]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h18443, hlam, p18461_0]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h18446, hlam, p18461_0]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h18448, hlam, p18461_0]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [hlam, p18461_0]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        rcases p18461_3 (m.d 0 1) (by simp) with h18497 | h18497
                        · rcases p18461_3 (m.d 0 2) (by simp) with h18498 | h18498
                          · rcases p18461_3 (m.d 0 3) (by simp) with h18499 | h18499
                            · rcases p18461_3 (m.d 0 4) (by simp) with h18500 | h18500
                              · rcases p18461_3 (m.d 0 5) (by simp) with h18501 | h18501
                                · linarith only [h18450, h18501, hlam]
                                · rcases h2bigk with h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c | h18503c
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [hlam, p18503_0]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h0, hlam, p18503_1]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h0, h18457, h18460, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18503_1]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    rcases p18503_3 (m.d 0 2) (by simp) with h18507 | h18507
                                    · rcases p18503_3 (m.d 1 2) (by simp) with h18508 | h18508
                                      · rcases p18503_3 (m.d 2 3) (by simp) with h18509 | h18509
                                        · linarith only [h18445, h18509, hlam]
                                        · linarith only [h18457, h18509, hlam]
                                      · linarith only [h18452, h18508, hlam]
                                    · linarith only [h18507, hlam, p18503_0]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    rcases p18503_3 (m.d 0 2) (by simp) with h18514 | h18514
                                    · rcases p18503_3 (m.d 1 2) (by simp) with h18515 | h18515
                                      · rcases p18503_3 (m.d 2 3) (by simp) with h18516 | h18516
                                        · linarith only [h18445, h18516, hlam]
                                        · linarith only [h18458, h18516, hlam]
                                      · linarith only [h18453, h18515, hlam]
                                    · linarith only [h18514, hlam, p18503_0]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h0, h18443, h18444, h18453, h18458, h18460, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18461_1, p18503_1]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [hlam, p18503_0]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h18457, h18460, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18503_1]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    rcases p18503_3 (m.d 0 2) (by simp) with h18524 | h18524
                                    · linarith only [h0, h18524, hlam]
                                    · linarith only [h18446, h18524, hlam]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h0, h18443, h18444, h18453, hlam, p18461_1, p18503_2]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h18445, hlam, p18503_0]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h18451, hlam, p18503_0]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [hlam, p18503_0]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h18445, h18457, h18460, hc02, hc45, hlam, hphi, ht0b, ht5b, p18503_1]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    rcases p18503_3 (m.d 0 2) (by simp) with h18532 | h18532
                                    · rcases p18503_3 (m.d 1 2) (by simp) with h18533 | h18533
                                      · rcases p18503_3 (m.d 2 3) (by simp) with h18534 | h18534
                                        · rcases p18503_3 (m.d 2 4) (by simp) with h18535 | h18535
                                          · linarith only [h18457, h18535, hlam]
                                          · linarith only [h18459, h18535, hlam]
                                        · linarith only [h18458, h18534, hlam]
                                      · linarith only [h18453, h18533, hlam]
                                    · linarith only [h18447, h18532, hlam]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h18446, hlam, p18503_0]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h18452, hlam, p18503_0]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h18457, hlam, p18503_1]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [hlam, p18503_0]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h15532, h18443, h18452, h18458, h18460, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p18503_1]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h18447, hlam, p18503_0]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h18453, hlam, p18503_0]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h18458, hlam, p18503_1]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [h18459, hlam, p18503_0]
                                  · have p18503_0 := h18503c.1
                                    have p18503_1 := h18503c.2.1
                                    have p18503_2 := h18503c.2.2.1
                                    have p18503_3 := h18503c.2.2.2
                                    linarith only [hlam, p18503_0]
                              · linarith only [h18450, h18500, hlam]
                            · linarith only [h18449, h18499, hlam]
                          · linarith only [h18447, h18498, hlam]
                        · linarith only [h18444, h18497, hlam]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h18444, hlam, p18461_0]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h18447, hlam, p18461_1]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h18449, hlam, p18461_0]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [h18450, hlam, p18461_1]
                      · have p18461_0 := h18461c.1
                        have p18461_1 := h18461c.2.1
                        have p18461_2 := h18461c.2.2.1
                        have p18461_3 := h18461c.2.2.2
                        linarith only [hlam, p18461_0]
                    · linarith only [h15532, h18443, h18451, h18456, h18460, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h15532, h18443, h18451, h18456, h18459, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h15532, h18444, h18451, h18455, h18457, h18458, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h18563 | h18563
                · linarith only [h15532, h18443, h18451, h18454, h18457, h18563, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h18565 | h18565
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h18566 | h18566
                    · rcases h0bigk with h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [hlam, p18567_0]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h0, hlam, p18567_1]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h15532, hlam, p18567_0]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h15532, h18443, h18451, h18455, h18456, h18563, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18567_1]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h15532, h18444, h18451, h18455, h18563, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18567_1]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h0, h18443, h18455, h18456, h18563, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18567_1]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [hlam, p18567_0]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h0, h15532, h18443, h18455, h18456, h18563, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18567_1]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        rcases p18567_3 (m.d 0 1) (by simp) with h18576 | h18576
                        · linarith only [h0, h18576, hlam]
                        · linarith only [h18443, h18576, hlam]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        rcases p18567_3 (m.d 0 1) (by simp) with h18579 | h18579
                        · linarith only [h0, h18579, hlam]
                        · linarith only [h18444, h18579, hlam]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h18443, h18455, h18456, h18563, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18567_1]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h18445, hlam, p18567_1]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [hlam, p18567_0]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        rcases p18567_3 (m.d 0 1) (by simp) with h18585 | h18585
                        · linarith only [h15532, h18585, hlam]
                        · linarith only [h18443, h18585, hlam]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        rcases p18567_3 (m.d 0 1) (by simp) with h18588 | h18588
                        · linarith only [h15532, h18588, hlam]
                        · linarith only [h18444, h18588, hlam]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h18443, hlam, p18567_0]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h18446, hlam, p18567_0]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h18448, hlam, p18567_0]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [hlam, p18567_0]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h0, h18443, h18444, h18455, h18563, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18567_1]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h18444, hlam, p18567_0]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h18447, hlam, p18567_1]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h18449, hlam, p18567_0]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [h18450, hlam, p18567_1]
                      · have p18567_0 := h18567c.1
                        have p18567_1 := h18567c.2.1
                        have p18567_2 := h18567c.2.2.1
                        have p18567_3 := h18567c.2.2.2
                        linarith only [hlam, p18567_0]
                    · linarith only [h15532, h18443, h18451, h18456, h18566, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h15532, h18443, h18451, h18456, h18565, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h18603 | h18603
              · rcases m.htr 2 3 5 (by decide) (by decide) with h18604 | h18604
                · rcases m.htr 2 4 5 (by decide) (by decide) with h18605 | h18605
                  · linarith only [h18452, h18456, h18605, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h18607 | h18607
                    · linarith only [h18454, h18456, h18607, hlam]
                    · rcases h0bigk with h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c | h18609c
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [hlam, p18609_0]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h0, hlam, p18609_1]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h15532, hlam, p18609_0]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h15532, h18450, h18451, h18456, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p18609_1]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h15532, h18450, h18451, h18452, h18456, h18603, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18609_1]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h0, h18443, h18450, h18452, h18456, h18603, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18609_1]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [hlam, p18609_0]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h0, h15532, h18443, h18450, h18452, h18456, h18603, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18609_1]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h0, h18450, h18452, h18456, h18603, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18609_1]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        rcases p18609_3 (m.d 0 1) (by simp) with h18619 | h18619
                        · linarith only [h0, h18619, hlam]
                        · linarith only [h18444, h18619, hlam]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h18443, h18450, h18452, h18456, h18603, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p18609_1]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h18445, hlam, p18609_1]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [hlam, p18609_0]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h15532, h18450, h18451, h18452, h18456, h18603, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18609_1]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        rcases p18609_3 (m.d 0 1) (by simp) with h18626 | h18626
                        · linarith only [h15532, h18626, hlam]
                        · linarith only [h18444, h18626, hlam]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h18443, hlam, p18609_0]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h18446, hlam, p18609_0]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h18448, hlam, p18609_0]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [hlam, p18609_0]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h0, h18443, h18450, h18452, h18456, h18603, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18609_1]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h18444, hlam, p18609_0]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h18447, hlam, p18609_1]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h18449, hlam, p18609_0]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [h18450, hlam, p18609_1]
                      · have p18609_0 := h18609c.1
                        have p18609_1 := h18609c.2.1
                        have p18609_2 := h18609c.2.2.1
                        have p18609_3 := h18609c.2.2.2
                        linarith only [hlam, p18609_0]
                · linarith only [h15532, h18443, h18450, h18451, h18455, h18456, h18603, h18604, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h15532, h18443, h18450, h18451, h18454, h18456, h18603, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h15532, h18449, h18455, hlam]
        · linarith only [h15532, h18448, h18454, hlam]
      · linarith only [h0, h18447, h18453, hlam]
    · linarith only [h0, h18446, h18452, hlam]
  · linarith only [h0, h18445, h18451, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  linarith only [h18443, h18450, h18651, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  linarith only [h18443, h18450, h18647, h18655, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  linarith only [h18443, h18450, h18647, h18653, h18657, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 1) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 1) ∧ (m.d 0 1) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 1) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [hlam, p18659_0]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 1) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 1) ∧ (m.d 0 2) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 2) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [h0, hlam, p18659_1]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x2 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 1) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 1) ∧ (m.d 0 3) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 3) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [h15532, hlam, p18659_0]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x3 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 1) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 1) ∧ (m.d 0 4) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 4) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  rcases p18659_3 (m.d 0 1) (by simp) with h18663 | h18663
  · rcases p18659_3 (m.d 0 2) (by simp) with h18664 | h18664
    · rcases p18659_3 (m.d 0 3) (by simp) with h18665 | h18665
      · rcases p18659_3 (m.d 0 4) (by simp) with h18666 | h18666
        · linarith only [h18443, h18666, hlam]
        · rcases p18659_3 (m.d 0 5) (by simp) with h18668 | h18668
          · linarith only [h18444, h18668, hlam]
          · linarith only [h18450, h18668, hlam]
      · linarith only [h18448, h18665, hlam]
    · linarith only [h18446, h18664, hlam]
  · linarith only [h18443, h18663, hlam]

end R2N4
