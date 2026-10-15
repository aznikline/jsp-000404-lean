import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S37
import Jsp000404.R1LeavesN7_0S60

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h19744 | h19744
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 h19744
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 h19744

set_option maxHeartbeats 63786000 in
set_option maxHeartbeats 63786000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s3 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s4 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 64034000 in
set_option maxHeartbeats 64034000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s2 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s3 m hb1 hb2 hb4 hb5 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h31897 | h31897
    · rcases m.htr 0 2 4 (by decide) (by decide) with h31898 | h31898
      · rcases m.htr 0 2 5 (by decide) (by decide) with h31899 | h31899
        · linarith only [h0, h3, h31899, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h31901 | h31901
          · rcases m.htr 0 3 5 (by decide) (by decide) with h31902 | h31902
            · linarith only [h0, h3, h31897, h31902, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h31904 | h31904
              · linarith only [h2, h3, h31904, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h31906 | h31906
                · rcases m.htr 1 2 4 (by decide) (by decide) with h31907 | h31907
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h31908 | h31908
                    · linarith only [h0, h3, h31899, h31908, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h31910 | h31910
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h31911 | h31911
                        · linarith only [h1, h3, h31902, h31911, hlam]
                        · linarith only [h0, h3, h31906, h31911, hc23, hc35, hlam, hphi]
                      · linarith only [h31901, h31902, h31910, hc13, hc35, hlam, hphi]
                  · linarith only [h31898, h31899, h31907, hc12, hc25, hlam, hphi]
                · linarith only [h31897, h31899, h31906, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h31917 | h31917
            · linarith only [h0, h3, h31898, h31901, h31917, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h31919 | h31919
              · linarith only [h0, h3, h31898, h31919, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h31921 | h31921
                · rcases m.htr 1 2 4 (by decide) (by decide) with h31922 | h31922
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h31923 | h31923
                    · linarith only [h0, h3, h31899, h31923, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h31925 | h31925
                      · linarith only [h1, h3, h31901, h31923, h31925, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h31927 | h31927
                        · linarith only [h1, h31917, h31927, hlam]
                        · linarith only [h0, h3, h31921, h31927, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h3, h31898, h31921, h31922, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h31897, h31899, h31921, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h31932 | h31932
        · linarith only [h2, h3, h31898, h31932, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h31934 | h31934
          · linarith only [h31897, h31898, h31934, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h31936 | h31936
            · linarith only [h2, h3, h31897, h31898, h31936, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h31938 | h31938
              · linarith only [h2, h3, h31938, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h31940 | h31940
                · rcases m.htr 1 2 4 (by decide) (by decide) with h31941 | h31941
                  · linarith only [h0, h31898, h31941, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h31943 | h31943
                    · linarith only [h0, h31932, h31943, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h31945 | h31945
                      · linarith only [h1, h3, h31934, h31943, h31945, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h31947 | h31947
                        · linarith only [h1, h31936, h31947, hlam]
                        · linarith only [h0, h3, h31940, h31947, hc23, hc35, hlam, hphi]
                · linarith only [h31897, h31898, h31940, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h31951 | h31951
      · rcases m.htr 0 2 5 (by decide) (by decide) with h31952 | h31952
        · linarith only [h1, h3, h31897, h31952, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h31954 | h31954
          · rcases m.htr 0 3 5 (by decide) (by decide) with h31955 | h31955
            · linarith only [h1, h3, h31955, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h31957 | h31957
              · linarith only [h1, h3, h31897, h31951, h31957, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h31959 | h31959
                · linarith only [h0, h3, h31897, h31959, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h31961 | h31961
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h31962 | h31962
                    · linarith only [h0, h3, h31952, h31962, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h31964 | h31964
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h31965 | h31965
                        · linarith only [h1, h3, h31955, h31962, h31965, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h31967 | h31967
                          · linarith only [h1, h2, h3, h31897, h31951, h31957, h31959, h31967, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h3, h31959, h31961, h31967, hc24, hc45, hlam, hphi]
                      · linarith only [h1, h3, h31954, h31959, h31961, h31964, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h31897, h31951, h31955, h31961, hc12, hc35, hlam, hphi, ht23]
          · linarith only [h31897, h31951, h31954, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h31973 | h31973
        · linarith only [h0, h3, h31973, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h31975 | h31975
          · rcases m.htr 0 3 5 (by decide) (by decide) with h31976 | h31976
            · linarith only [h1, h3, h31976, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h31978 | h31978
              · linarith only [h1, h3, h31975, h31978, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h31980 | h31980
                · linarith only [h0, h31897, h31980, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h31982 | h31982
                  · linarith only [h0, h31951, h31982, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h31984 | h31984
                    · linarith only [h0, h3, h31973, h31984, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h31986 | h31986
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h31987 | h31987
                        · linarith only [h1, h31976, h31987, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h31989 | h31989
                          · linarith only [h2, h3, h31978, h31989, hlam]
                          · linarith only [h1, h3, h31986, h31989, hc34, hc45, hlam, hphi]
                      · linarith only [h31975, h31976, h31986, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h31993 | h31993
            · linarith only [h1, h3, h31993, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h31995 | h31995
              · linarith only [h2, h3, h31995, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h31997 | h31997
                · linarith only [h0, h3, h31897, h31997, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h31999 | h31999
                  · linarith only [h1, h31951, h31975, h31997, h31999, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h32001 | h32001
                    · linarith only [h0, h31973, h32001, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h32003 | h32003
                      · linarith only [h1, h31975, h32003, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h32005 | h32005
                        · linarith only [h0, h1, h3, h31975, h31993, h32005, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h32007 | h32007
                          · linarith only [h2, h31995, h32007, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h32009 | h32009
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h32010 | h32010
                              · linarith only [h0, h3, h32005, h32010, hc12, hc23, hlam, hphi]
                              · linarith only [h1, h31975, h31997, h32009, h32010, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h32013 | h32013
                              · linarith only [h1, h31993, h31997, h32009, h32013, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h32015 | h32015
                                · linarith only [h2, h3, h31997, h32003, h32007, h32015, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h32017 | h32017
                                  · linarith only [h0, h31897, h32009, h32015, h32017, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h31897, h32009, h32017, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 64674000 in
set_option maxHeartbeats 64674000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s2 m hb1 hb2 hb4 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h32020 | h32020
    · rcases m.htr 0 2 3 (by decide) (by decide) with h32021 | h32021
      · rcases m.htr 0 2 4 (by decide) (by decide) with h32022 | h32022
        · linarith only [h0, h2, h32022, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h32024 | h32024
          · rcases m.htr 0 3 4 (by decide) (by decide) with h32025 | h32025
            · linarith only [h1, h2, h32025, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h32027 | h32027
              · rcases m.htr 0 4 5 (by decide) (by decide) with h32028 | h32028
                · rcases m.htr 1 2 3 (by decide) (by decide) with h32029 | h32029
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h32030 | h32030
                    · linarith only [h0, h2, h32022, h32024, h32030, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h32032 | h32032
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32033 | h32033
                        · linarith only [h1, h2, h32025, h32030, h32033, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h2, h32029, h32033, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h32024, h32029, h32032, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h32021, h32022, h32029, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h32027, h32028, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h32039 | h32039
                · rcases m.htr 1 2 3 (by decide) (by decide) with h32040 | h32040
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h32041 | h32041
                    · linarith only [h0, h2, h32022, h32041, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h32043 | h32043
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32044 | h32044
                        · linarith only [h1, h32025, h32044, hlam]
                        · linarith only [h0, h2, h32040, h32044, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h32024, h32040, h32041, h32043, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h32021, h32022, h32040, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h32024, h32039, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h32050 | h32050
            · linarith only [h1, h2, h32050, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h32052 | h32052
              · linarith only [h32021, h32024, h32052, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h32054 | h32054
                · rcases m.htr 1 2 3 (by decide) (by decide) with h32055 | h32055
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h32056 | h32056
                    · linarith only [h0, h2, h32022, h32056, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h32058 | h32058
                      · linarith only [h0, h32024, h32058, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32060 | h32060
                        · linarith only [h1, h2, h32050, h32060, hlam]
                        · linarith only [h0, h2, h32055, h32060, hc23, hc34, hlam, hphi]
                  · linarith only [h32021, h32022, h32055, hc12, hc24, hlam, hphi]
                · linarith only [h2, h32020, h32054, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h32065 | h32065
        · linarith only [h0, h2, h32065, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h32067 | h32067
          · rcases m.htr 0 3 4 (by decide) (by decide) with h32068 | h32068
            · linarith only [h1, h2, h32068, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h32070 | h32070
              · rcases m.htr 0 4 5 (by decide) (by decide) with h32071 | h32071
                · rcases m.htr 1 2 3 (by decide) (by decide) with h32072 | h32072
                  · linarith only [h0, h2, h32021, h32067, h32072, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h32074 | h32074
                    · linarith only [h0, h32065, h32074, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h32076 | h32076
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32077 | h32077
                        · linarith only [h1, h2, h32068, h32077, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h32079 | h32079
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h32080 | h32080
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h32081 | h32081
                              · linarith only [h1, h2, h32077, h32079, h32081, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h32083 | h32083
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h32084 | h32084
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h32085 | h32085
                                    · rcases h1bigk with h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c | h32086c
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [hlam, p32086_0]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h2, h32076, h32083, h32085, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p32086_1]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h2, h32072, h32076, h32083, h32085, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p32086_1]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h2, hlam, p32086_0]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        rcases p32086_3 (m.d 0 1) (by simp) with h32091 | h32091
                                        · rcases p32086_3 (m.d 1 2) (by simp) with h32092 | h32092
                                          · linarith only [h0, h32092, hlam]
                                          · linarith only [h32076, h32092, hlam]
                                        · linarith only [h32091, hlam, p32086_0]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h0, hlam, p32086_0]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [hlam, p32086_0]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h32072, hlam, p32086_1]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h32074, hlam, p32086_1]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h0, h2, h32074, h32081, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p32086_1]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h1, hlam, p32086_0]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h1, h2, h32074, h32081, hc12, hc34, hlam, hphi, ht23, p32086_1]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [hlam, p32086_0]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h32077, hlam, p32086_0]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h1, h2, h32074, h32076, h32081, h32083, h32085, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p32086_1]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h1, h32074, h32081, hc13, hc34, hlam, hphi, p32086_1]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        rcases p32086_3 (m.d 0 1) (by simp) with h32107 | h32107
                                        · linarith only [h2, h32107, hlam]
                                        · linarith only [h0, h32107, hlam]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        rcases p32086_3 (m.d 0 1) (by simp) with h32110 | h32110
                                        · linarith only [h2, h32110, hlam]
                                        · linarith only [h1, h32110, hlam]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [hlam, p32086_0]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        rcases p32086_3 (m.d 0 1) (by simp) with h32114 | h32114
                                        · linarith only [h2, h32114, hlam]
                                        · linarith only [h32020, h32114, hlam]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h32020, hlam, p32086_0]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h32076, hlam, p32086_0]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h32079, hlam, p32086_0]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [h32080, hlam, p32086_0]
                                      · have p32086_0 := h32086c.1
                                        have p32086_1 := h32086c.2.1
                                        have p32086_2 := h32086c.2.2.1
                                        have p32086_3 := h32086c.2.2.2
                                        linarith only [hlam, p32086_0]
                                    · linarith only [h1, h2, h32072, h32074, h32081, h32085, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h2, h32072, h32074, h32076, h32080, h32083, h32084, hc15, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h32021, h32070, h32076, h32083, hc03, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h1, h2, h32072, h32076, h32080, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h1, h2, h32070, h32072, h32076, h32079, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h2, h32067, h32074, h32076, hc12, hc24, hlam, hphi]
                · linarith only [h2, h32020, h32071, hlam]
              · linarith only [h32021, h32067, h32070, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h32130 | h32130
            · linarith only [h1, h2, h32130, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h32132 | h32132
              · rcases m.htr 0 4 5 (by decide) (by decide) with h32133 | h32133
                · rcases m.htr 1 2 3 (by decide) (by decide) with h32134 | h32134
                  · linarith only [h0, h2, h32021, h32134, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h32136 | h32136
                    · linarith only [h0, h32065, h32136, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h32138 | h32138
                      · linarith only [h0, h32067, h32138, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32140 | h32140
                        · linarith only [h1, h2, h32130, h32136, h32140, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h32142 | h32142
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h32143 | h32143
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h32144 | h32144
                              · linarith only [h0, h2, h32140, h32144, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h32146 | h32146
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h32147 | h32147
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h32148 | h32148
                                    · rcases h1bigk with h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c | h32149c
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [hlam, p32149_0]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h2, h32136, hc12, hc24, hlam, hphi, p32149_1]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h2, h32136, h32144, hc13, hc34, hlam, hphi, p32149_1]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h2, hlam, p32149_0]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h2, h32136, h32138, h32144, hc12, hc34, hlam, hphi, ht23, p32149_1]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h0, hlam, p32149_0]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [hlam, p32149_0]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h32134, hlam, p32149_1]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h32136, hlam, p32149_1]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h32138, hlam, p32149_1]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h1, hlam, p32149_0]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h1, h2, h32136, h32144, hc12, hc34, hlam, hphi, ht23, p32149_1]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [hlam, p32149_0]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h32140, hlam, p32149_0]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h1, h2, h32136, h32138, h32144, hc12, hc34, hlam, hphi, ht23, p32149_1]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h1, h32136, h32144, hc13, hc34, hlam, hphi, p32149_1]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        rcases p32149_3 (m.d 0 1) (by simp) with h32166 | h32166
                                        · linarith only [h2, h32166, hlam]
                                        · linarith only [h0, h32166, hlam]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        rcases p32149_3 (m.d 0 1) (by simp) with h32169 | h32169
                                        · linarith only [h2, h32169, hlam]
                                        · linarith only [h1, h32169, hlam]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [hlam, p32149_0]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        rcases p32149_3 (m.d 0 1) (by simp) with h32173 | h32173
                                        · linarith only [h2, h32173, hlam]
                                        · linarith only [h32020, h32173, hlam]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h32020, hlam, p32149_0]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h2, h32020, h32136, h32144, hc12, hc34, hlam, hphi, ht23, p32149_1]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h32142, hlam, p32149_0]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [h32143, hlam, p32149_0]
                                      · have p32149_0 := h32149c.1
                                        have p32149_1 := h32149c.2.1
                                        have p32149_2 := h32149c.2.2.1
                                        have p32149_3 := h32149c.2.2.2
                                        linarith only [hlam, p32149_0]
                                    · linarith only [h0, h2, h32136, h32144, h32148, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h2, h32136, h32142, h32143, h32147, hlam]
                                · linarith only [h1, h2, h32142, h32146, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h1, h2, h32138, h32142, h32143, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1, h2, h32132, h32140, h32142, hc13, hc34, hlam, hphi]
                · linarith only [h2, h32020, h32133, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h32187 | h32187
                · rcases m.htr 1 2 3 (by decide) (by decide) with h32188 | h32188
                  · linarith only [h0, h32021, h32188, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h32190 | h32190
                    · linarith only [h0, h32065, h32190, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h32192 | h32192
                      · linarith only [h0, h32067, h32192, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32194 | h32194
                        · linarith only [h1, h2, h32130, h32194, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h32196 | h32196
                          · linarith only [h1, h32132, h32196, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h32198 | h32198
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h32199 | h32199
                              · linarith only [h2, h32020, h32188, h32194, h32196, h32199, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h32201 | h32201
                                · linarith only [h1, h32132, h32188, h32199, h32201, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h32203 | h32203
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h32204 | h32204
                                    · rcases h1bigk with h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c | h32205c
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [hlam, p32205_0]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h2, h32190, hc12, hc24, hlam, hphi, p32205_1]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h2, h32188, h32190, hc12, hc24, hlam, hphi, p32205_1]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h2, hlam, p32205_0]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h2, h32188, h32190, h32196, hc12, hc24, hlam, hphi, p32205_1]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h0, hlam, p32205_0]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [hlam, p32205_0]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h32188, hlam, p32205_1]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h32190, hlam, p32205_1]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h32192, hlam, p32205_1]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h1, hlam, p32205_0]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h1, h2, h32190, hc12, hc24, hlam, hphi, p32205_1]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [hlam, p32205_0]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h32194, hlam, p32205_0]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h32196, hlam, p32205_1]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h0, h32190, hc12, hc24, hlam, hphi, p32205_1]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        rcases p32205_3 (m.d 0 1) (by simp) with h32222 | h32222
                                        · linarith only [h2, h32222, hlam]
                                        · linarith only [h0, h32222, hlam]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        rcases p32205_3 (m.d 0 1) (by simp) with h32225 | h32225
                                        · linarith only [h2, h32225, hlam]
                                        · linarith only [h1, h32225, hlam]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [hlam, p32205_0]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        rcases p32205_3 (m.d 0 1) (by simp) with h32229 | h32229
                                        · linarith only [h2, h32229, hlam]
                                        · linarith only [h32020, h32229, hlam]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h32020, hlam, p32205_0]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h2, h32020, h32190, h32199, hc12, hc34, hlam, hphi, ht23, p32205_1]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h2, h32020, h32190, h32199, hc13, hc34, hlam, hphi, p32205_1]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [h32198, hlam, p32205_0]
                                      · have p32205_0 := h32205c.1
                                        have p32205_1 := h32205c.2.1
                                        have p32205_2 := h32205c.2.2.1
                                        have p32205_3 := h32205c.2.2.2
                                        linarith only [hlam, p32205_0]
                                    · linarith only [h2, h32020, h32190, h32198, h32199, h32204, hlam]
                                  · linarith only [h2, h32020, h32190, h32198, h32203, hlam]
                            · linarith only [h0, h2, h32198, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h2, h32020, h32187, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h32241 | h32241
      · rcases m.htr 0 2 4 (by decide) (by decide) with h32242 | h32242
        · linarith only [h0, h2, h32242, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h32244 | h32244
          · linarith only [h0, h32020, h32244, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h32246 | h32246
            · linarith only [h1, h2, h32246, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h32248 | h32248
              · linarith only [h0, h32020, h32241, h32248, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h32250 | h32250
                · rcases m.htr 1 2 3 (by decide) (by decide) with h32251 | h32251
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h32252 | h32252
                    · linarith only [h0, h2, h32242, h32252, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h32254 | h32254
                      · linarith only [h0, h32020, h32244, h32254, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32256 | h32256
                        · linarith only [h0, h32020, h32246, h32250, h32251, h32256, hlam]
                        · linarith only [h0, h2, h32251, h32256, hc23, hc34, hlam, hphi]
                  · linarith only [h32241, h32242, h32251, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h32260 | h32260
                  · linarith only [h0, h2, h32250, h32260, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2, h32241, h32250, h32260, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h32263 | h32263
        · linarith only [h1, h2, h32241, h32263, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h32265 | h32265
          · linarith only [h1, h32020, h32241, h32265, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h32267 | h32267
            · linarith only [h1, h2, h32267, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h32269 | h32269
              · linarith only [h1, h32020, h32269, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h32271 | h32271
                · rcases m.htr 1 2 3 (by decide) (by decide) with h32272 | h32272
                  · linarith only [h0, h2, h32241, h32272, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h32274 | h32274
                    · linarith only [h0, h32020, h32263, h32271, h32274, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h32276 | h32276
                      · linarith only [h1, h2, h32265, h32272, h32274, h32276, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32278 | h32278
                        · linarith only [h1, h2, h32267, h32274, h32278, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h32280 | h32280
                          · linarith only [h1, h32020, h32269, h32280, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h32282 | h32282
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h32283 | h32283
                              · linarith only [h0, h32020, h32278, h32282, h32283, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h32285 | h32285
                                · linarith only [h1, h32020, h32272, h32280, h32283, h32285, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h32287 | h32287
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h32288 | h32288
                                    · rcases h1bigk with h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c | h32289c
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [hlam, p32289_0]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h32020, h32276, hc12, hc25, hlam, hphi, p32289_1]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h32020, h32272, h32276, hc12, hc25, hlam, hphi, p32289_1]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h2, hlam, p32289_0]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h32020, hlam, p32289_0]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h0, hlam, p32289_0]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [hlam, p32289_0]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h32272, hlam, p32289_1]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h32274, hlam, p32289_1]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h32276, hlam, p32289_1]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h1, hlam, p32289_0]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h1, h32020, h32276, hc12, hc25, hlam, hphi, p32289_1]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [hlam, p32289_0]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h32278, hlam, p32289_0]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h32280, hlam, p32289_1]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h0, h32274, h32283, hc12, hc34, hlam, hphi, ht23, p32289_1]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        rcases p32289_3 (m.d 0 1) (by simp) with h32306 | h32306
                                        · linarith only [h2, h32306, hlam]
                                        · linarith only [h0, h32306, hlam]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        rcases p32289_3 (m.d 0 1) (by simp) with h32309 | h32309
                                        · linarith only [h2, h32309, hlam]
                                        · linarith only [h1, h32309, hlam]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [hlam, p32289_0]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h1, h32020, h32272, h32274, h32283, hc12, hc34, hlam, hphi, ht23, p32289_1]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h1, h32272, h32276, h32285, h32288, hc12, hc34, hlam, hphi, ht23, p32289_1]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        rcases p32289_3 (m.d 0 1) (by simp) with h32315 | h32315
                                        · linarith only [h32020, h32315, hlam]
                                        · linarith only [h0, h32315, hlam]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        rcases p32289_3 (m.d 0 1) (by simp) with h32318 | h32318
                                        · linarith only [h32020, h32318, hlam]
                                        · linarith only [h1, h32318, hlam]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [h32282, hlam, p32289_0]
                                      · have p32289_0 := h32289c.1
                                        have p32289_1 := h32289c.2.1
                                        have p32289_2 := h32289c.2.2.1
                                        have p32289_3 := h32289c.2.2.2
                                        linarith only [hlam, p32289_0]
                                    · linarith only [h1, h2, h32271, h32272, h32274, h32283, h32288, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h2, h32271, h32274, h32287, hlam]
                            · linarith only [h2, h32271, h32282, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h32326 | h32326
                  · linarith only [h0, h32241, h32326, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h32328 | h32328
                    · linarith only [h0, h32263, h32328, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h32330 | h32330
                      · linarith only [h0, h32265, h32330, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32332 | h32332
                        · linarith only [h0, h1, h32020, h32241, h32267, h32332, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h32334 | h32334
                          · linarith only [h1, h32269, h32334, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h32336 | h32336
                            · linarith only [h0, h2, h32271, h32332, h32336, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h2, h32326, h32336, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
