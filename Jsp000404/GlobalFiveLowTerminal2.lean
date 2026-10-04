import Jsp000404.GlobalFiveLowStrongModel

namespace Jsp404.GlobalFiveLowTerminal

set_option maxHeartbeats 32000000 in
theorem model_impossible_2 {n delta : ℝ} (m : FiveModel n delta 2) : False := by
  have hn := m.hn
  obtain ⟨hdelta0, hdelta1⟩ := m.hdelta
  obtain ⟨h010, h011⟩ := m.range 0 1 (by decide)
  obtain ⟨h020, h021⟩ := m.range 0 2 (by decide)
  obtain ⟨h030, h031⟩ := m.range 0 3 (by decide)
  obtain ⟨h040, h041⟩ := m.range 0 4 (by decide)
  obtain ⟨h120, h121⟩ := m.range 1 2 (by decide)
  obtain ⟨h130, h131⟩ := m.range 1 3 (by decide)
  obtain ⟨h140, h141⟩ := m.range 1 4 (by decide)
  obtain ⟨h230, h231⟩ := m.range 2 3 (by decide)
  obtain ⟨h240, h241⟩ := m.range 2 4 (by decide)
  obtain ⟨h340, h341⟩ := m.range 3 4 (by decide)
  have hc10 := m.symm 1 0
  have hc20 := m.symm 2 0
  have hc30 := m.symm 3 0
  have hc40 := m.symm 4 0
  have hc21 := m.symm 2 1
  have hc31 := m.symm 3 1
  have hc41 := m.symm 4 1
  have hc32 := m.symm 3 2
  have hc42 := m.symm 4 2
  have hc43 := m.symm 4 3
  rcases m.triangle 0 1 2 (by decide) (by decide) with ⟨ht012a,ht012b,ht012c,ht012d,ht012e⟩ | ⟨ht012a,ht012b,ht012c,ht012d,ht012e⟩
  ·
    rcases m.triangle 0 1 3 (by decide) (by decide) with ⟨ht013a,ht013b,ht013c,ht013d,ht013e⟩ | ⟨ht013a,ht013b,ht013c,ht013d,ht013e⟩
    ·
      rcases m.triangle 0 1 4 (by decide) (by decide) with ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩ | ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 0 2 3 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h010, h341, ht123a, ht234a, hbg1]
                      ·
                        linarith only [hdelta1, h010, ht012a, h341, ht123c, ht234a, hbg1]
                      ·
                        have hb3 := m.budget 3 (by decide) 0 1 2 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hn, hdelta1, h020, h141, ht023b, hbg3, hbg1]
                        ·
                          linarith only [hdelta1, h010, ht012a, h341, ht123b, hbg3, ht234a]
                        ·
                          linarith only [hdelta1, h010, ht012a, h341, ht123a, hbg3]
                        ·
                          linarith only [hn, hdelta1, ht013c, hbg3, ht134c, hbg1]
                        ·
                          linarith only [hdelta1, h030, h141, hbg1, hbg3a]
                        ·
                          linarith only [hdelta1, h030, h141, hbg1, hbg3a]
                        ·
                          linarith only [hdelta1, h030, h141, hbg1, hbg3a]
                        ·
                          linarith only [hdelta1, h010, ht012a, h341, ht123b, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, hbg3b, ht134c, hbg1]
                        ·
                          linarith only [hdelta1, ht013c, ht124c, ht234c, hbg3b, hbg1]
                      ·
                        have hb3 := m.budget 3 (by decide) 0 1 2 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hn, hdelta1, ht013b, ht134b, hbg1, hbg3]
                        ·
                          linarith only [hdelta1, h010, ht012a, h341, ht123b, ht234a, hbg3]
                        ·
                          linarith only [hdelta1, h010, ht012a, h341, ht123a, hbg3]
                        ·
                          linarith only [hdelta1, ht012a, ht014c, ht123a, ht034b, ht234a, hbg1, hbg3]
                        ·
                          linarith only [hdelta1, ht012b, ht023b, ht134b, hbg1, hbg3a]
                        ·
                          linarith only [hdelta1, ht012b, ht023b, ht134b, hbg1, hbg3a]
                        ·
                          linarith only [hdelta1, ht012b, ht023b, ht134b, hbg1, hbg3a]
                        ·
                          linarith only [hdelta1, h010, h341, ht013a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, ht012a, ht014c, ht123a, ht034b, hbg3c, hbg1]
                      ·
                        linarith only [hdelta1, h010, h341, hbg1c, ht134a]
                      ·
                        have hb3 := m.budget 3 (by decide) 0 1 2 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h010, h341, ht012b, ht023b, ht124c, ht234c, hbg3, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h231, ht123b, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, h010, h341, ht123a, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, ht013c, ht124c, ht234c, hbg3, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h341, ht012b, ht023b, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h341, ht012b, ht023b, ht124c, ht123a, hbg1c, ht234c, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h231, ht124c, ht123a, hbg1c, ht234c, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h341, ht013a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h341, ht013c, ht124c, ht123a, hbg1c, ht234c, hbg3c]
                      ·
                        have hb3 := m.budget 3 (by decide) 0 1 2 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht123a, ht134b, ht023e, hbg1c, hbg3]
                        ·
                          linarith only [hdelta1, h010, h341, ht013a, ht234a, hbg3]
                        ·
                          linarith only [hdelta1, h010, h341, ht123a, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, ht014c, ht123a, ht034b, hbg1c, ht234a, hbg3]
                        ·
                          linarith only [hdelta1, h010, h341, ht012b, ht023b, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h341, ht012b, ht023b, ht123a, ht134b, hbg1c, hbg3c]
                        ·
                          linarith only [hdelta1, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h341, ht123b, hbg3c, hbg1a]
                        ·
                          linarith only [hdelta1, ht013c, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, ht014c, ht123a, ht034b, hbg1c, hbg3c]
                      ·
                        linarith only [hdelta1, h010, ht012a, h341, ht124c, hbg1c, ht234c]
                      ·
                        linarith only [hdelta1, ht012a, ht134b, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c]
                    ·
                      have hb3 := m.budget 3 (by decide) 0 1 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc30, hc31, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht023e, ht234a, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, h010, h231, ht013a, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht023e, hbg3]
                      ·
                        linarith only [hdelta1, ht013c, ht234a, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, h030, h231, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023e, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht234a, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, h010, h231, ht013a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013c, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, hbg3c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht134a, ht123c, ht234a]
                    ·
                      have hb3 := m.budget 3 (by decide) 0 4 1 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc30, hc31, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht013e, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht023e, ht123c, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht023e, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht134a, ht123c, hbg3]
                      ·
                        linarith only [hdelta1, ht023e, hbg3c, ht123c]
                      ·
                        linarith only [hdelta1, ht023e, hbg3c, ht134a]
                      ·
                        linarith only [hdelta1, hbg3c, ht134a, ht123c]
                      ·
                        linarith only [hdelta1, ht034a, ht023e, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, hbg3c, ht123c]
                      ·
                        linarith only [hdelta1, ht034a, hbg3c, ht134a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht123b, ht134b, ht124c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht123c, ht234a, ht134a]
                    ·
                      have hb3 := m.budget 3 (by decide) 0 4 1 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc30, hc31, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht023e, ht123c, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht023e, ht123c, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht234b, ht123b, ht023e, ht124a, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht234b, ht123a, ht124a, hbg3]
                      ·
                        linarith only [hdelta1, ht013e, hbg3c]
                      ·
                        linarith only [hdelta1, ht234b, ht123b, ht023e, ht124a, hbg3c]
                      ·
                        linarith only [hdelta1, ht234b, ht123a, ht124a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht023e, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123c, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht234b, ht123b, ht124a, hbg3c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 0 3 2 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        have hb3 := m.budget 3 (by decide) 0 2 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc32, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h010, h241, ht012b, ht023b, ht123a, ht124a, hbg3]
                        ·
                          linarith only [hdelta1, h010, h341, ht012b, ht023a, ht123c, ht234c, ht124a, hbg3]
                        ·
                          linarith only [hn, hdelta1, h010, h341, hbg1, hbg3]
                        ·
                          linarith only [hdelta1, ht023c, ht123a, ht234c, ht124a, hbg3]
                        ·
                          linarith only [hdelta1, h010, h341, ht012b, ht023b, ht123c, ht234c, ht124a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h341, hbg1, hbg3b]
                        ·
                          linarith only [hdelta1, ht123a, hbg3c, ht234c, ht124a]
                        ·
                          linarith only [hdelta1, h010, h341, hbg1, hbg3b]
                        ·
                          linarith only [hdelta1, ht023c, ht123c, ht234c, ht124a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h341, hbg1, hbg3a]
                      ·
                        linarith only [hdelta1, h010, h241, ht013a, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht023a, ht123a, ht124c, ht234c, hbg1]
                      ·
                        linarith only [hdelta1, ht012b, ht023a, ht123a, ht124b, hbg1]
                      ·
                        linarith only [hdelta1, h010, h341, ht234c, ht124a, hbg1c]
                      ·
                        have hb3 := m.budget 3 (by decide) 0 2 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc32, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h030, h341, ht123a, ht124c, ht234c, hbg3, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h341, ht012b, ht023a, ht123c, ht124c, ht234c, hbg3, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h341, hbg1a, hbg3]
                        ·
                          linarith only [hdelta1, ht023c, ht123a, ht124c, ht234c, hbg3, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h341, ht012b, ht023b, ht123c, ht124c, ht234c, hbg3c, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h341, ht012b, ht023b, ht123a, ht124c, ht234c, hbg3c, hbg1c]
                        ·
                          linarith only [hdelta1, ht123a, ht124c, ht234c, hbg3c, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h341, ht012b, ht023a, hbg3c]
                        ·
                          linarith only [hdelta1, ht023c, ht123c, ht124c, ht234c, hbg3c, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h341, ht023c, ht123a, ht124c, ht234c, hbg3c, hbg1c]
                      ·
                        have hb3 := m.budget 3 (by decide) 0 2 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc32, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h010, h241, ht012b, ht023b, ht123a, ht124a, hbg3]
                        ·
                          linarith only [hdelta1, ht012b, ht023a, ht123c, ht124b, hbg3, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h341, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, ht023c, ht123a, ht234c, ht124a, hbg3]
                        ·
                          linarith only [hdelta1, ht012b, ht023b, ht123c, ht124b, hbg3c, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h341, ht012b, ht023b, ht123a, ht124b, hbg3c, hbg1c]
                        ·
                          linarith only [hdelta1, ht123a, ht234c, ht124a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h341, ht012b, ht023a, hbg3c]
                        ·
                          linarith only [hdelta1, ht023c, ht123c, ht234c, ht124a, hbg3c]
                        ·
                          linarith only [hdelta1, ht023c, ht123a, ht124b, hbg3c, hbg1c]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht023a, ht123b, ht124c, ht234c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012b, ht023a, ht123b, ht124b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                    ·
                      linarith only [ht123a, ht124b, ht134c, ht234a]
                  ·
                    linarith only [ht123c, ht124b, ht134c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb0 := m.budget 0 (by decide) 1 2 3 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        linarith only [hdelta1, h010, h121, ht023a, ht123a, hbg0]
                      ·
                        linarith only [hdelta1, ht012e, ht023c, ht124a, hbg0, ht234b]
                      ·
                        linarith only [hdelta1, ht012e, ht023b, ht024c, ht124a, hbg0]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 3 4 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          have hb3 := m.budget 3 (by decide) 0 2 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012e, ht023b, ht123a, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht023a, ht123c, hbg3]
                          ·
                            linarith only [hn, hdelta1, h010, h341, hbg1, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht034b, ht134a, hbg0, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, h010, h341, ht012b, ht023b, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h341, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht034b, ht134a, hbg0, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, h010, h341, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht034b, ht134a, hbg0, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, h010, h341, hbg3a, hbg1]
                        ·
                          linarith only [hdelta1, ht012e, ht023a, ht123b, ht124c, hbg1]
                        ·
                          linarith only [hdelta1, ht012e, ht024a, ht124b, hbg1]
                        ·
                          linarith only [hdelta1, ht012b, ht023a, ht123a, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 0 2 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012e, ht023b, ht123a, hbg3]
                          ·
                            linarith only [hdelta1, h121, h230, ht124c, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, h010, h341, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, ht034b, ht134a, hbg0, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, ht012e, ht023b, ht124c, hbg3c, hbg1b]
                          ·
                            linarith only [hdelta1, h010, h341, ht012e, ht023b, ht123b, ht124c, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, ht034b, hbg3b, hbg0, hbg1c, ht134c]
                          ·
                            linarith only [hdelta1, h020, h341, ht023a, hbg3c]
                          ·
                            linarith only [hdelta1, ht034b, hbg0, hbg1c, ht134c, hbg3b]
                          ·
                            linarith only [hdelta1, ht034b, hbg0, hbg1c, ht134c, hbg3b]
                        ·
                          have hb3 := m.budget 3 (by decide) 0 2 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012e, ht023b, ht123a, hbg3]
                          ·
                            linarith only [hdelta1, h121, h230, ht134b, hbg1b, hbg3]
                          ·
                            linarith only [hdelta1, h010, h341, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, ht034b, ht134a, hbg0, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht023b, ht134b, hbg3c, hbg1b]
                          ·
                            linarith only [hdelta1, h010, h341, ht012e, ht023b, ht123b, ht134b, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht123b, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h341, ht012e, ht023a, ht134b, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, ht034b, hbg0, hbg3c, hbg1a]
                        ·
                          have hb3 := m.budget 3 (by decide) 0 2 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012b, ht023b, ht123a, hbg1b, hbg3]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, ht134b, hbg1b, ht124c, hbg3]
                          ·
                            linarith only [hdelta1, h010, h341, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, ht034b, ht134a, hbg0, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, ht012b, ht023b, ht134b, hbg1b, hbg3c, ht124c]
                          ·
                            linarith only [hdelta1, h010, h341, ht012b, ht023b, hbg1c, ht124a, hbg3c, ht234b]
                          ·
                            linarith only [hdelta1, ht134a, hbg1c, ht124a, hbg3c, ht234b]
                          ·
                            linarith only [hdelta1, h020, h341, ht023a, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, ht034b, hbg3c, hbg0, hbg1a]
                        ·
                          linarith only [hdelta1, h010, h121, ht013a, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht023a, ht123b, hbg1c, ht124c]
                        ·
                          linarith only [hdelta1, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, h010, h341, ht023c, ht123b, ht134a, hbg0c]
                      ·
                        linarith only [hdelta1, h010, h121, ht023b, ht024c, ht124a, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 0 2 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc32, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h010, h131, ht023b, ht123b, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h010, h341, ht023a, ht134a, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h010, h341, ht013c, ht023b, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, ht023a, ht123b, ht034b, ht134a, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, h010, h131, ht023b, hbg0a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h341, ht023b, ht123b, hbg0a, hbg3c]
                        ·
                          linarith only [hdelta1, ht123b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h341, ht023a, hbg0a, hbg3c]
                        ·
                          linarith only [hdelta1, ht023a, ht034b, ht134a, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht023a, ht123b, ht034b, hbg0c, hbg3c]
                      ·
                        linarith only [hdelta1, h020, h121, ht024c, ht124a, hbg0c]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 3 4 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          have hb3 := m.budget 3 (by decide) 0 2 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h020, h231, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h020, h141, ht023c, ht134b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h341, ht012b, ht013c, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht034b, ht134a, hbg1, hbg0b, hbg3]
                          ·
                            linarith only [hdelta1, h010, h341, ht012b, ht134a, hbg3c, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h341, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, h010, h121, ht123a, ht134a, hbg1, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h341, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, ht023c, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h341, hbg1, hbg3a]
                        ·
                          linarith only [hdelta1, h010, h141, ht012b, ht013c, hbg1, hbg0a]
                        ·
                          linarith only [hdelta1, ht012e, ht014c, ht034b, hbg1, hbg0a]
                        ·
                          linarith only [hdelta1, ht012b, ht023c, ht123a, hbg1, hbg0a]
                        ·
                          linarith only [hdelta1, ht012e, ht034b, ht124c, hbg1c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012e, ht034b, ht134b, hbg1c, hbg0c]
                        ·
                          have hb3 := m.budget 3 (by decide) 0 2 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012b, ht124a, ht234b, hbg3, hbg0a, hbg1b]
                          ·
                            linarith only [hdelta1, h010, h131, ht012b, ht023c, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h341, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, ht024c, ht034b, ht134a, ht124a, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht012b, ht134b, ht124c, hbg0a, hbg3c, hbg1b]
                          ·
                            linarith only [hdelta1, h010, h341, ht012b, ht123b, hbg0a, hbg3c]
                          ·
                            linarith only [hdelta1, ht134a, ht124a, ht234b, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h341, ht012b, ht023a, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht124a, ht234b, hbg1c, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h121, ht012b, ht023c, ht123b, hbg0a, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht023c, ht123b, ht124c, hbg0a, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht024c, ht034b, ht124b, hbg0a, hbg1c]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 3 4 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          have hb3 := m.budget 3 (by decide) 0 2 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012e, ht023b, ht123a, hbg3]
                          ·
                            linarith only [hdelta1, h020, h341, ht023a, ht134a, hbg3]
                          ·
                            linarith only [hn, hdelta1, h010, h341, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht134a, hbg1, hbg3, hbg0b, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h341, ht012b, ht023b, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h341, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, ht134a, hbg1, hbg0c, hbg3b]
                          ·
                            linarith only [hdelta1, h010, h341, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, ht134a, hbg1, hbg0c, hbg3b]
                          ·
                            linarith only [hdelta1, h010, h341, hbg3a, hbg1]
                        ·
                          linarith only [hdelta1, ht012e, ht013a, ht023b, hbg1, ht124c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012e, ht014a, ht023b, hbg1, hbg0c]
                        ·
                          linarith only [hdelta1, ht012b, ht023a, ht123a, hbg1]
                        ·
                          linarith only [hdelta1, ht012e, ht023b, ht124c, hbg1c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012e, ht023b, ht134b, hbg1c, hbg0c]
                        ·
                          have hb3 := m.budget 3 (by decide) 0 2 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012e, ht023b, ht123a, hbg3]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, ht123c, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, h010, h341, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, ht034c, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h341, ht012b, ht023b, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h341, ht012b, ht023b, ht123a, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, ht134a, hbg3c, ht124a, ht234b, hbg1c]
                          ·
                            linarith only [hdelta1, h010, h341, ht012b, ht023a, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, ht024c, hbg3c, ht124a, hbg1c, hbg0a]
                        ·
                          linarith only [hdelta1, h010, h121, ht012b, ht023a, ht123b, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht023a, ht123b, ht124c, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht023b, ht024c, ht124b, hbg1c, hbg0a]
                    ·
                      linarith only [ht123b, ht134a, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 0 2 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc30, hc32, hc31] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht012e, ht023b, ht123a, hbg3]
                      ·
                        linarith only [hdelta1, ht012e, ht023a, ht123c, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht012e, ht023a, ht123c, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, ht023c, ht134a, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, ht012e, ht023b, ht123c, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht012e, ht023b, ht123c, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht134a, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, h010, h131, ht012b, ht023a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023c, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, hbg3c]
                    ·
                      have hb3 := m.budget 3 (by decide) 0 4 2 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc30, hc32, hc31] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht023e, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht012e, ht023b, ht034a, ht123a, hbg3]
                      ·
                        linarith only [hdelta1, h020, h131, ht023b, ht034a, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht123b, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht012e, ht023b, ht123a, hbg3c]
                      ·
                        linarith only [hdelta1, ht012e, ht023b, ht123c, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht123b, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht012e, ht034c, ht024b, ht123c, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123b, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, hbg3c, ht234a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb0 := m.budget 0 (by decide) 1 2 4 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht013d, ht024a, ht234d, hbg3, hbg0]
                        ·
                          linarith only [hn, hdelta1, h010, h231, ht023b, ht123c, hbg3, hbg0]
                        ·
                          linarith only [hn, hdelta1, h010, h231, ht013c, ht024b, ht034c, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht013d, ht023a, ht034a, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, h010, h131, ht023b, hbg3b, hbg0]
                        ·
                          linarith only [hdelta1, h010, h231, ht013c, ht024b, ht034c, hbg3b, hbg0]
                        ·
                          linarith only [hdelta1, ht012c, ht013d, ht234c, ht124a, hbg3c, hbg0]
                        ·
                          linarith only [hdelta1, h010, h131, ht023b, hbg3a, hbg0]
                        ·
                          linarith only [hdelta1, h010, h131, ht023b, hbg3a, hbg0]
                        ·
                          linarith only [hdelta1, h010, h231, ht013c, ht024b, ht034c, hbg3a, hbg0]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 2 4 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht013d, ht124a, ht234d, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, h010, h231, ht034a, ht123c, ht124a, ht234d, hbg1, hbg3]
                          ·
                            linarith only [hn, hdelta1, h010, h231, ht012b, ht013c, ht034c, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht013d, ht034a, ht123a, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, h010, h131, ht012b, ht034c, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht013c, ht034c, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, ht013d, ht234c, ht124a, hbg1, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h131, ht012b, ht034c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h010, h131, ht012b, ht034c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht013c, ht034c, hbg3a, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012a, ht013d, ht134d, hbg1, hbg3]
                          ·
                            linarith only [hn, hdelta1, h010, h131, ht012b, ht034c, hbg0, hbg3]
                          ·
                            linarith only [hn, hdelta1, h010, h231, ht012b, ht013c, ht034c, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht013d, ht034a, ht134c, ht123c, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht034c, ht123c, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, h120, h231, ht134c, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, ht012a, ht013d, ht134c, ht123c, hbg3c, hbg1]
                          ·
                            linarith only [hdelta1, h010, ht012a, h231, ht134c, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, h010, h131, ht012b, ht034c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht013c, ht034c, hbg3a, hbg0]
                        ·
                          linarith only [hn, hdelta1, h010, h131, ht012b, ht014c, hbg1, hbg0]
                        ·
                          linarith only [hn, hdelta1, ht012b, ht013c, ht034c, hbg1, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht013d, ht134d, hbg1c, hbg3]
                          ·
                            linarith only [hdelta1, h010, h231, ht034a, ht124c, ht123c, hbg1c, ht234d, hbg3]
                          ·
                            linarith only [hn, hdelta1, h010, h231, ht012b, ht013c, ht034c, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht013d, ht034a, ht134c, ht123c, hbg1c, hbg3]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht034c, ht123c, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht014c, ht134c, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, ht013d, ht134c, ht123c, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h231, ht134c, hbg1c, hbg3b]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht034c, ht123c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h010, h231, ht134c, hbg1c, hbg3a]
                        ·
                          linarith only [hdelta1, h010, h131, ht012b, ht014c, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, ht012b, ht013c, ht034c, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, h010, h131, ht012b, ht014c, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, ht012b, ht013c, ht034c, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, h010, h131, ht012b, ht014c, hbg0, hbg1a]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb1 := m.budget 1 (by decide) 0 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht013d, ht024e, ht124a, hbg0, hbg1]
                          ·
                            linarith only [hdelta1, ht012a, ht013d, ht014e, hbg0, hbg1]
                          ·
                            have hb4 := m.budget 4 (by decide) 3 0 1 2 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc40, hc41, hc42] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hn, hdelta1, ht012a, h231, h340, ht013d, ht123c, ht124b, hbg4, hbg0, hbg1]
                            ·
                              linarith only [hn, hdelta1, h040, h231, ht123c, hbg4, hbg1]
                            ·
                              linarith only [hdelta1, ht012a, ht013d, ht034b, ht124b, ht234d, hbg4, hbg0]
                            ·
                              linarith only [hdelta1, ht012a, ht013d, ht034b, ht124a, hbg4, hbg0]
                            ·
                              linarith only [hdelta1, ht012a, h231, h340, ht013d, hbg4a, ht123c, ht124b, hbg0, hbg1]
                            ·
                              linarith only [hdelta1, ht012a, h231, h340, ht013d, hbg4a, ht123c, ht124b, hbg0, hbg1]
                            ·
                              linarith only [hdelta1, ht012a, h231, h340, ht013d, hbg4a, ht123c, ht124b, hbg0, hbg1]
                            ·
                              linarith only [hdelta1, h040, h231, hbg4a, ht123c, hbg1]
                            ·
                              linarith only [hdelta1, h040, h231, hbg4a, ht123c, hbg1]
                            ·
                              linarith only [hdelta1, ht012a, ht013d, ht034b, hbg4c, ht124b, hbg0]
                          ·
                            linarith only [hn, hdelta1, ht013c, ht014b, hbg0, hbg1]
                          ·
                            linarith only [hdelta1, ht013d, ht034b, ht124c, hbg1c, ht234d, hbg0]
                          ·
                            have hb4 := m.budget 4 (by decide) 3 0 1 2 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc40, hc41, hc42] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hn, hdelta1, h231, h340, ht013d, ht123c, hbg1c, ht124b, hbg4, hbg0]
                            ·
                              linarith only [hdelta1, h040, h231, ht123c, hbg4, hbg1b]
                            ·
                              linarith only [hdelta1, h010, h241, hbg1a, ht124b, hbg4]
                            ·
                              linarith only [hdelta1, ht013d, ht034b, ht124a, hbg1a, hbg4, hbg0]
                            ·
                              linarith only [hdelta1, h231, h340, ht013c, ht123c, hbg4a, hbg0]
                            ·
                              linarith only [hdelta1, h231, h340, ht013c, ht123c, hbg4a, hbg0]
                            ·
                              linarith only [hdelta1, h231, h340, ht013c, ht123c, hbg4a, hbg0]
                            ·
                              linarith only [hdelta1, ht024e, hbg4c]
                            ·
                              linarith only [hdelta1, h010, h131, ht034b, ht124a, hbg1c, hbg4c]
                            ·
                              linarith only [hdelta1, h010, h031, ht034b, hbg1a, ht124b, hbg0, hbg4c]
                          ·
                            linarith only [hdelta1, ht012b, ht013c, ht024b, hbg1b, hbg0]
                          ·
                            linarith only [hdelta1, h010, ht012a, h231, hbg1c, ht123c]
                          ·
                            linarith only [hdelta1, ht012b, ht013c, ht024b, hbg1b, hbg0]
                          ·
                            linarith only [hdelta1, ht012b, ht013c, ht024b, hbg1b, hbg0]
                        ·
                          linarith only [hn, hdelta1, h010, h131, ht012b, ht024b, hbg0, hbg3]
                        ·
                          linarith only [hn, hdelta1, h010, h231, ht012b, ht013c, ht024b, hbg0, hbg3]
                        ·
                          linarith only [hn, hdelta1, ht023c, ht034b, hbg0, hbg3]
                        ·
                          linarith only [hdelta1, h010, h131, ht012b, ht024b, hbg3b, hbg0]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht013c, ht024b, hbg3b, hbg0]
                        ·
                          linarith only [hdelta1, ht023c, ht034b, hbg3b, hbg0]
                        ·
                          linarith only [hdelta1, h010, h131, ht012b, ht024b, hbg3a, hbg0]
                        ·
                          linarith only [hdelta1, h010, h131, ht012b, ht024b, hbg3a, hbg0]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht013c, ht024b, hbg3a, hbg0]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc40, hc41, hc42] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht012a, ht034c, ht124a, ht234d, hbg4, hbg0]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht034a, ht124a, ht234d, hbg1, hbg0]
                          ·
                            linarith only [hdelta1, ht012a, ht034a, ht124c, ht234d, hbg1, hbg0]
                          ·
                            linarith only [hn, hdelta1, h040, h231, ht123c, hbg4, hbg1]
                          ·
                            linarith only [hn, hdelta1, ht012b, ht024b, ht134c, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, ht034a, ht124c, hbg1c, ht234d, hbg0]
                          ·
                            linarith only [hdelta1, h040, h231, ht123c, hbg1b, hbg4]
                          ·
                            linarith only [hdelta1, ht012b, ht024b, ht134c, hbg1b, hbg4]
                          ·
                            linarith only [hdelta1, h010, h131, ht012b, ht024b, hbg1b, hbg4]
                          ·
                            linarith only [hdelta1, ht012b, ht024b, ht134c, hbg1b, hbg4]
                          ·
                            linarith only [hdelta1, h010, h131, ht012b, ht024b, hbg4, hbg1a]
                        ·
                          linarith only [hdelta1, ht012a, ht034a, ht124b, ht234d, hbg4, hbg0]
                        ·
                          linarith only [hdelta1, ht012a, ht034a, ht124a, hbg4, hbg0]
                        ·
                          linarith only [hdelta1, ht124c, ht234d, hbg4c]
                        ·
                          linarith only [hdelta1, ht014a, ht034c, ht234d, hbg0, hbg4c]
                        ·
                          linarith only [hdelta1, ht012a, ht034c, ht124a, hbg0, hbg4c]
                        ·
                          linarith only [hdelta1, ht024e, hbg4c]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht034a, hbg4b, ht124a, hbg0, hbg1]
                          ·
                            linarith only [hdelta1, ht012a, ht034a, ht124c, hbg4b, hbg0, hbg1]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht024b, ht123c, hbg4a, hbg1]
                          ·
                            linarith only [hdelta1, ht012b, ht024b, ht134c, hbg4a, hbg1]
                          ·
                            linarith only [hdelta1, ht034a, ht124c, hbg4b, hbg0, hbg1c]
                          ·
                            linarith only [hdelta1, h010, h231, ht034b, ht123c, ht124a, hbg1c, hbg4c]
                          ·
                            linarith only [hdelta1, ht034b, ht134c, ht124a, hbg1c, hbg4c]
                          ·
                            linarith only [hdelta1, h010, ht012a, h131, hbg1c]
                          ·
                            linarith only [hdelta1, ht012a, ht134c, hbg1c]
                          ·
                            linarith only [hdelta1, ht014a, hbg1c]
                        ·
                          linarith only [hdelta1, ht012a, ht034a, ht124b, hbg4c, hbg0]
                      ·
                        linarith only [hdelta1, ht014d, hbg0c]
                      ·
                        linarith only [hdelta1, ht013d, ht024b, hbg0c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc40, hc41, hc42] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht012c, ht034c, hbg0c, ht124a, ht234d, hbg4]
                        ·
                          linarith only [hdelta1, h010, h141, ht024b, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h010, h231, ht014c, ht024b, ht234c, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, ht034a, ht024a, hbg0c, hbg4]
                        ·
                          linarith only [hdelta1, ht124c, hbg4c, ht234d]
                        ·
                          linarith only [hdelta1, ht014c, hbg4c, ht234d]
                        ·
                          linarith only [hdelta1, ht024a, ht034c, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, h010, h231, ht024b, hbg4c, ht234c, hbg0a]
                        ·
                          linarith only [hdelta1, ht024b, ht034a, ht124c, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht014c, ht024b, ht034a, hbg0c, hbg4c]
                      ·
                        linarith only [hdelta1, ht012b, ht013d, hbg0c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc40, hc41, hc42] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          have hb1 := m.budget 1 (by decide) 0 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht123a, ht034c, hbg4, hbg1, hbg0b]
                          ·
                            linarith only [hdelta1, ht012a, h141, h340, ht034c, hbg4, hbg1, hbg0b]
                          ·
                            linarith only [hdelta1, h131, h340, ht014a, ht034c, hbg4, hbg1, hbg0b]
                          ·
                            linarith only [hdelta1, ht012b, ht013c, ht034c, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, ht124c, ht034c, hbg1c, hbg4, ht234d, hbg0b]
                          ·
                            linarith only [hdelta1, h131, h340, ht014c, hbg4, hbg1b]
                          ·
                            linarith only [hdelta1, ht013c, ht034c, ht124a, hbg4, ht234d, hbg1c]
                          ·
                            linarith only [hdelta1, h131, h340, ht014c, hbg4, hbg1b]
                          ·
                            linarith only [hdelta1, ht012a, ht134c, hbg1c]
                          ·
                            linarith only [hdelta1, h131, h340, ht014c, hbg4, hbg1a]
                        ·
                          linarith only [hdelta1, h010, h141, ht012b, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h010, h241, ht012b, ht014c, hbg4, hbg0a]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht034a, ht124a, hbg4, hbg1, hbg0b]
                          ·
                            linarith only [hdelta1, ht012a, ht034a, ht124c, hbg4, hbg1, hbg0b]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht014c, ht123c, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, ht012b, ht013c, ht034c, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, ht034a, ht124c, hbg4, hbg0b, hbg1c]
                          ·
                            have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc30, hc31, hc32] at hb3
                            rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                              ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                              ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                            ·
                              linarith only [hdelta1, ht124a, hbg4, hbg1a, hbg0b, hbg3]
                            ·
                              linarith only [hdelta1, h010, h131, ht034a, ht124a, hbg4, hbg1a, hbg3]
                            ·
                              linarith only [hdelta1, h010, h231, ht013c, ht034a, ht124a, hbg4, hbg1a, hbg3]
                            ·
                              linarith only [hdelta1, ht012b, ht014c, ht034a, hbg0c, ht123c, ht124a, hbg4, hbg0b, hbg1c, hbg3]
                            ·
                              linarith only [hdelta1, h010, h131, ht012b, ht014c, hbg0c, ht124a, hbg4, hbg3a, hbg1c]
                            ·
                              linarith only [hdelta1, h010, h131, ht012b, ht014c, hbg0c, ht124a, hbg4, hbg3a, hbg1c]
                            ·
                              linarith only [hdelta1, h010, h131, ht012b, ht014c, hbg0c, ht124a, hbg4, hbg3a, hbg1c]
                            ·
                              linarith only [hdelta1, h010, h231, ht012b, ht014c, ht034a, hbg0c, ht124a, hbg4, hbg3b, hbg1c]
                            ·
                              linarith only [hdelta1, ht034a, ht123c, hbg3c]
                            ·
                              linarith only [hdelta1, h010, h231, ht012b, ht014c, ht034a, hbg0c, ht124a, hbg4, hbg3a, hbg1c]
                          ·
                            linarith only [hdelta1, ht013c, ht034a, ht124a, hbg4, hbg1c]
                          ·
                            linarith only [hdelta1, h010, ht012a, h131, hbg1c]
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht034a, ht124c, hbg4, hbg1c]
                          ·
                            linarith only [hdelta1, ht012b, ht014c, hbg0a, hbg1c]
                        ·
                          linarith only [hdelta1, ht134d, hbg4c]
                        ·
                          linarith only [hdelta1, ht014c, hbg4c, ht234d]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht034c, ht124a, hbg4c, hbg0b, hbg1]
                          ·
                            linarith only [hdelta1, ht012a, ht124c, ht034c, hbg4c, hbg0b, hbg1]
                          ·
                            linarith only [hdelta1, h131, h340, ht014c, hbg4a, hbg1]
                          ·
                            linarith only [hdelta1, ht012b, ht013c, ht034c, hbg0a, hbg1]
                          ·
                            linarith only [hdelta1, ht124c, ht034c, hbg4c, hbg0b, hbg1c]
                          ·
                            linarith only [hdelta1, h010, h231, ht014c, ht123c, ht124a, hbg4c, hbg1c]
                          ·
                            linarith only [hdelta1, ht013c, ht034c, ht124a, hbg4c, hbg1c]
                          ·
                            linarith only [hdelta1, h010, ht012a, h231, ht123c, hbg1c]
                          ·
                            linarith only [hdelta1, ht012a, ht134c, hbg1c]
                          ·
                            linarith only [hdelta1, ht014a, hbg1c]
                        ·
                          linarith only [hdelta1, h010, h241, ht012b, hbg4c, hbg0a]
                        ·
                          linarith only [hdelta1, ht012b, ht034a, ht124c, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht012b, ht014c, ht034a, hbg0c, hbg4c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc40, hc41, hc42] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h031, h340, hbg4, hbg0a]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht034b, hbg0c, ht124a, ht234d, hbg1]
                          ·
                            linarith only [hdelta1, ht012a, ht034b, ht124c, hbg0c, ht234d, hbg1]
                          ·
                            linarith only [hn, hdelta1, h020, h231, ht024b, ht123c, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, ht012b, ht013c, ht024b, hbg0a, hbg1]
                          ·
                            linarith only [hdelta1, ht034b, ht124c, hbg0c, hbg1c, ht234d]
                          ·
                            linarith only [hdelta1, h040, h231, ht123c, hbg4, hbg1b]
                          ·
                            linarith only [hdelta1, ht012b, ht024b, ht134c, hbg4, hbg1b]
                          ·
                            linarith only [hdelta1, h010, h131, ht012b, ht024b, hbg4, hbg1b]
                          ·
                            linarith only [hdelta1, ht012b, ht024b, ht134c, hbg4, hbg1b]
                          ·
                            linarith only [hdelta1, h010, h131, ht012b, ht024b, hbg4, hbg1a]
                        ·
                          linarith only [hdelta1, ht012a, ht034b, hbg0c, hbg4, ht124b, ht234d]
                        ·
                          linarith only [hdelta1, ht012a, ht034b, hbg0c, hbg4, ht124a]
                        ·
                          linarith only [hdelta1, ht124c, hbg4c, ht234d]
                        ·
                          linarith only [hdelta1, ht014a, hbg4c, hbg0c, ht234d]
                        ·
                          linarith only [hdelta1, ht012b, ht024a, hbg4c, hbg0c]
                        ·
                          linarith only [hdelta1, ht024e, hbg4c]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht034b, hbg0c, ht124a, hbg4b, hbg1]
                          ·
                            linarith only [hdelta1, ht012a, ht014e, hbg0c, hbg1]
                          ·
                            linarith only [hdelta1, h040, h231, ht123c, hbg1, hbg4a]
                          ·
                            linarith only [hdelta1, ht012b, ht013c, ht024b, hbg0a, hbg1]
                          ·
                            linarith only [hdelta1, ht034b, ht124c, hbg0c, hbg1c, hbg4b]
                          ·
                            linarith only [hdelta1, h010, h231, ht034b, hbg4c, ht123c, ht124a, hbg1c]
                          ·
                            linarith only [hdelta1, ht034b, hbg4c, ht134c, ht124a, hbg1c]
                          ·
                            linarith only [hdelta1, h010, ht012a, h231, ht123c, hbg1c]
                          ·
                            linarith only [hdelta1, ht012a, ht134c, hbg1c]
                          ·
                            linarith only [hdelta1, ht014a, hbg1c]
                        ·
                          linarith only [hdelta1, ht012a, ht034b, hbg0c, hbg4c, ht124b]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb1 := m.budget 1 (by decide) 0 4 2 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        have hb4 := m.budget 4 (by decide) 3 0 2 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc40, hc42, hc41] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h231, h340, ht024c, ht123a, ht124a, hbg4]
                        ·
                          linarith only [hdelta1, h040, h231, ht123a, ht124a, hbg4]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht123a, ht024a, ht124c, hbg4]
                        ·
                          have hb0 := m.budget 0 (by decide) 1 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, h010, h231, ht123a, ht024a, ht124a, hbg0]
                          ·
                            linarith only [hdelta1, h020, h231, ht024c, ht123a, ht124a, hbg0]
                          ·
                            linarith only [hn, hdelta1, ht013d, ht034b, hbg4, hbg1, hbg0]
                          ·
                            linarith only [hn, hdelta1, ht034a, hbg4, hbg1, hbg0]
                          ·
                            linarith only [hdelta1, h010, h231, ht024c, ht123a, ht124a, hbg0c]
                          ·
                            linarith only [hdelta1, ht013d, ht034b, hbg0b, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, ht034a, hbg0b, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, ht013d, ht034b, hbg0b, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, ht034a, hbg0b, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, ht034a, hbg0b, hbg4, hbg1]
                        ·
                          linarith only [hdelta1, h231, h340, ht123a, ht124a, hbg4c]
                        ·
                          linarith only [hdelta1, h231, h340, ht024c, ht123a, ht124c, hbg4c]
                        ·
                          linarith only [hdelta1, h010, h231, ht024c, ht123a, ht124a, hbg4c, hbg1]
                        ·
                          linarith only [hdelta1, h020, h231, ht024b, ht123a, ht124c, hbg4c]
                        ·
                          linarith only [hdelta1, h010, h231, ht034b, ht123a, ht124a, hbg4c, hbg1]
                        ·
                          have hb0 := m.budget 0 (by decide) 1 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, h010, h231, ht123a, ht024a, ht124c, hbg4a, hbg0]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht024c, ht123a, ht124c, hbg4a, hbg0]
                          ·
                            linarith only [hdelta1, ht013d, ht034b, hbg1, hbg4b, hbg0]
                          ·
                            linarith only [hdelta1, ht012b, ht034a, ht024a, hbg4c, hbg0]
                          ·
                            linarith only [hdelta1, h010, h031, ht024c, ht034a, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht013d, ht024b, hbg0c]
                          ·
                            linarith only [hdelta1, ht034a, ht024a, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012b, ht013d, hbg0c]
                          ·
                            linarith only [hdelta1, ht012b, ht024c, ht034a, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012b, ht034b, ht024a, hbg4c, hbg0c]
                      ·
                        linarith only [hdelta1, h010, h231, ht014a, ht123a, hbg1]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht024a, ht123c, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, ht012b, ht123b, ht024a, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, h010, h231, ht123a, hbg1c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 0 2 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc40, hc42, hc41] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h231, h340, ht014c, ht124c, ht123c, hbg1b, hbg4]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht024b, ht123c, hbg1b, ht124a, hbg4]
                        ·
                          linarith only [hdelta1, h231, h240, ht124c, ht123c, hbg1b, hbg4]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht013d, hbg1a, hbg4, hbg3]
                          ·
                            linarith only [hdelta1, h010, h131, ht034a, hbg1a, hbg4, hbg3]
                          ·
                            linarith only [hdelta1, h010, h231, ht124c, hbg1a, hbg1b, hbg3]
                          ·
                            linarith only [hdelta1, ht014c, ht034b, ht124c, ht123c, hbg1b, hbg3]
                          ·
                            linarith only [hdelta1, h010, h231, hbg1a, ht123c, hbg4, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h231, ht124c, hbg3b, hbg1c]
                          ·
                            linarith only [hdelta1, ht013d, ht124c, ht123c, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h231, ht124c, hbg3b, hbg1c]
                          ·
                            linarith only [hdelta1, ht034a, ht123c, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h231, ht124c, hbg3a, hbg1c]
                        ·
                          linarith only [hdelta1, h121, h340, ht124a, hbg4c]
                        ·
                          linarith only [hdelta1, h231, h340, ht024c, ht124c, ht123c, hbg1b, hbg4c]
                        ·
                          linarith only [hdelta1, h010, h231, ht024c, ht123c, ht124a, hbg4c, hbg1c]
                        ·
                          linarith only [hdelta1, h020, h231, ht024b, ht124c, ht123c, hbg1b, hbg4c]
                        ·
                          linarith only [hdelta1, h010, h231, ht034b, ht123c, ht124a, hbg4c, hbg1c]
                        ·
                          have hb0 := m.budget 0 (by decide) 1 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, h010, h121, ht024a, ht124c, hbg0, hbg4a]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht024c, ht124c, hbg0, ht123c, hbg1b, hbg4a]
                          ·
                            linarith only [hdelta1, ht012b, ht013d, ht034b, ht024a, hbg0, hbg4c]
                          ·
                            linarith only [hdelta1, ht012b, ht034a, ht024a, hbg0, hbg4c]
                          ·
                            linarith only [hdelta1, h010, h231, ht024c, ht124c, ht123c, hbg1b, hbg4a, hbg0c]
                          ·
                            linarith only [hdelta1, ht013d, ht024b, hbg0c]
                          ·
                            linarith only [hdelta1, ht034a, ht024a, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012b, ht013d, hbg0c]
                          ·
                            linarith only [hdelta1, ht012b, ht024c, ht034a, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012b, ht034b, ht024a, hbg4c, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb4 := m.budget 4 (by decide) 3 0 2 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc40, hc42, hc41] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht024c, ht123a, hbg4, ht124a]
                          ·
                            linarith only [hdelta1, h040, h231, ht123a, hbg4, ht124a]
                          ·
                            linarith only [hdelta1, ht012b, ht123b, ht024a, ht124c, hbg4, hbg1b]
                          ·
                            linarith only [hdelta1, ht013c, hbg4, hbg1b, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h231, h340, ht123a, ht124a, hbg4c]
                          ·
                            linarith only [hdelta1, h231, h340, ht024c, ht123a, ht124c, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, hbg3, hbg4b, hbg1c]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht024b, ht123a, ht124c, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, hbg4b, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht013c, hbg4b, hbg3, hbg1c]
                        ·
                          linarith only [hdelta1, ht013b, hbg1b, hbg3]
                        ·
                          linarith only [hdelta1, h010, h231, ht123b, ht124c, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, ht034b, ht024c, ht123a, ht124a, hbg3]
                        ·
                          linarith only [hdelta1, h231, h340, ht123a, ht124c, hbg3c, hbg1c]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 0 2 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc40, hc42, hc41] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht014c, ht123b, ht124c, hbg4, hbg3b]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht024b, ht123b, ht124a, hbg4, hbg3b]
                          ·
                            linarith only [hdelta1, h231, h240, ht123b, ht124c, hbg4, hbg3b]
                          ·
                            linarith only [hdelta1, ht013c, hbg4, hbg1c, hbg3a]
                          ·
                            linarith only [hdelta1, h231, h340, ht123b, hbg4c, ht124a, hbg3b]
                          ·
                            linarith only [hdelta1, h231, h340, ht024c, ht123b, ht124c, hbg4c, hbg3b]
                          ·
                            linarith only [hdelta1, ht024c, ht123b, hbg4c, ht124a, hbg1c]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht024b, ht123b, ht124c, hbg4c, hbg3b]
                          ·
                            linarith only [hdelta1, ht034b, ht123b, hbg4c, ht124a, hbg1c]
                          ·
                            linarith only [hdelta1, h010, h231, ht012b, ht013c, ht024a, hbg4c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht123a, ht124c, hbg3c, hbg1c]
                        ·
                          linarith only [hdelta1, h231, h340, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, ht034a, hbg3c, ht123c]
                        ·
                          linarith only [hdelta1, ht013c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, h010, h131, ht012b, ht024a, hbg1c, ht124b]
                      ·
                        linarith only [hdelta1, ht012b, ht123b, ht024a, hbg1c, ht124b]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht023c, ht034a, ht134a, ht123b]
                  ·
                    linarith only [ht123c, ht134c, ht124b]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb0 := m.budget 0 (by decide) 1 2 4 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        linarith only [hdelta1, h010, h121, ht023a, ht123a, hbg0]
                      ·
                        linarith only [hdelta1, ht012e, ht024c, ht123a, ht234c, hbg0]
                      ·
                        linarith only [hdelta1, ht012e, ht023c, ht024b, ht123a, hbg0]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 2 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht134d, hbg1, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht023b, ht123a, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht023a, ht123c, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht034a, ht134c, hbg1, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht134d, hbg1, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht134d, hbg1, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht134d, hbg1, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht013e, hbg3c]
                          ·
                            linarith only [hdelta1, ht034a, ht134c, hbg3b, hbg1, hbg0]
                          ·
                            linarith only [hdelta1, ht034a, ht134c, hbg3b, hbg1, hbg0]
                        ·
                          linarith only [hdelta1, ht012e, ht123c, ht124b, ht024a, hbg1]
                        ·
                          linarith only [hdelta1, ht012e, ht023a, ht123b, hbg1]
                        ·
                          linarith only [hdelta1, ht012b, ht123a, ht024a, ht234c, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 2 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h121, h340, ht123c, hbg1c, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht012e, ht023b, ht123a, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht023a, ht123c, hbg3]
                          ·
                            linarith only [hdelta1, ht014c, ht034b, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, h121, h340, ht123c, hbg1c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h121, h340, ht123c, hbg1c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h121, h340, ht123c, hbg1c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, ht012e, ht024b, ht123c, ht034c, hbg3c]
                          ·
                            linarith only [hdelta1, ht034a, hbg1c, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, ht034a, hbg1c, hbg3b, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 2 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h121, h340, ht134c, hbg1c, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, h030, h121, ht123b, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, h121, h230, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, ht034a, ht134c, hbg3, hbg1a, hbg0]
                          ·
                            linarith only [hdelta1, h121, h340, ht134c, hbg1c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h121, h340, ht134c, hbg1c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h121, h340, ht134c, hbg1c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h030, h121, hbg3c, hbg1b]
                          ·
                            linarith only [hdelta1, ht034a, ht123b, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht034a, hbg3c]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 2 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht134d, hbg1a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht012b, ht024b, ht123a, ht034c, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, ht123c, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, ht034a, ht134c, hbg1a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht123a, ht134d, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht123c, ht134d, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht123a, ht134c, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht012b, ht024b, ht123c, ht034c, hbg1b, hbg3c]
                          ·
                            linarith only [hdelta1, ht034a, ht123b, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h121, ht014a, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht123c, ht124b, ht024a, hbg1c]
                        ·
                          linarith only [hdelta1, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, ht013d, ht034c, hbg0c]
                      ·
                        linarith only [hdelta1, h010, h121, ht023c, ht024b, ht123a, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 2 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc32, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h121, h340, ht023a, ht123a, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, h010, h121, ht023b, ht123a, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h010, h121, ht123c, ht024a, ht234c, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, ht034a, ht024a, ht123b, ht234c, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, h121, h340, ht123a, hbg3c]
                        ·
                          linarith only [hdelta1, h121, h340, ht023a, ht123c, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht024a, ht123b, ht234c, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h121, ht024b, ht123c, ht034c, hbg0a, hbg3c]
                        ·
                          linarith only [hdelta1, ht034a, ht123b, hbg3c]
                        ·
                          linarith only [hdelta1, ht023c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht012e, ht013c, ht123c, hbg0c]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          have hb4 := m.budget 4 (by decide) 3 0 2 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc40, hc42, hc41] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht134d, ht034c, hbg1, hbg0b, hbg4]
                          ·
                            linarith only [hdelta1, h020, h241, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h141, ht012b, ht024c, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, ht034a, hbg1, hbg0b, hbg4]
                          ·
                            linarith only [hdelta1, h121, h340, ht124a, hbg4c]
                          ·
                            linarith only [hdelta1, ht024c, ht134d, hbg4c]
                          ·
                            linarith only [hdelta1, ht034c, hbg1, hbg4c, hbg0b]
                          ·
                            linarith only [hdelta1, ht012e, ht123c, ht134c, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, ht012b, ht034a, ht124b, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012b, ht024c, ht034a, hbg4c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012e, ht014c, ht123c, hbg1, hbg0a]
                        ·
                          linarith only [hdelta1, h010, h121, ht012b, ht023c, ht034c, ht123b, hbg1, hbg0a]
                        ·
                          linarith only [hdelta1, ht012b, ht023c, ht123a, ht034c, hbg1, hbg0a]
                        ·
                          linarith only [hdelta1, ht012e, ht123c, ht034c, hbg1c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012e, ht134c, ht034c, hbg1c, hbg0c]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 2 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht023c, ht123a, ht134d, hbg1c, hbg3]
                          ·
                            linarith only [hdelta1, ht013b, ht123a, hbg1b, hbg3]
                          ·
                            linarith only [hdelta1, ht012b, ht023c, ht123c, ht034c, hbg1b, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, ht023c, ht034a, ht123a, ht134c, hbg1c, hbg3]
                          ·
                            linarith only [hdelta1, h121, h340, ht123a, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht123c, ht134d, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, ht023c, ht123a, ht134c, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, ht012b, ht123c, ht034c, hbg3c, hbg1b, hbg0a]
                          ·
                            linarith only [hdelta1, ht034a, ht123b, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, ht012e, ht024c, ht124b, hbg1c, hbg0a]
                        ·
                          linarith only [hdelta1, ht012b, ht024c, ht123c, ht124b, hbg1c, hbg0a]
                        ·
                          linarith only [hdelta1, ht012b, ht023c, ht034c, ht123b, hbg1c, hbg0a]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          have hb4 := m.budget 4 (by decide) 3 0 2 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc40, hc42, hc41] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hn, hdelta1, h131, h340, ht134c, hbg0c, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, ht012e, ht024b, ht124a, hbg4]
                          ·
                            linarith only [hdelta1, ht012e, ht123c, ht024a, ht134c, hbg4]
                          ·
                            linarith only [hdelta1, h010, h121, ht023c, ht034b, ht123a, hbg0a, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, ht134d, hbg4a, hbg0c, hbg1]
                          ·
                            linarith only [hdelta1, ht134d, hbg4a, hbg0c, hbg1]
                          ·
                            linarith only [hdelta1, hbg4b, hbg4a, hbg0c, hbg1]
                          ·
                            linarith only [hdelta1, ht014e, hbg4c]
                          ·
                            linarith only [hdelta1, ht034b, hbg0c, hbg4b, hbg1]
                          ·
                            linarith only [hdelta1, ht034b, hbg0c, hbg4b, hbg1]
                        ·
                          linarith only [hdelta1, ht012e, ht123c, ht124b, ht024a, hbg1]
                        ·
                          linarith only [hdelta1, ht012e, ht013a, ht024b, hbg0c, hbg1]
                        ·
                          linarith only [hdelta1, ht012b, ht023c, ht024b, ht123a, hbg0a, hbg1]
                        ·
                          linarith only [hdelta1, ht012e, ht024b, ht123c, hbg1c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012e, ht024b, ht134c, hbg1c, hbg0c]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 2 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc32, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht023c, ht123a, ht134d, hbg1c, hbg3]
                          ·
                            linarith only [hdelta1, ht013b, ht123a, hbg1b, hbg3]
                          ·
                            linarith only [hdelta1, h040, h131, ht023c, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht013c, ht034b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h121, h340, ht123a, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht123c, ht134d, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht123a, ht134c, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht012b, ht024b, ht123c, hbg3c, hbg1b, hbg0a]
                          ·
                            linarith only [hdelta1, ht034b, ht123b, hbg3c, hbg0a]
                          ·
                            linarith only [hdelta1, ht023c, ht034b, hbg3c, hbg0a]
                        ·
                          linarith only [hdelta1, h010, h121, ht014a, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht123c, ht124b, ht024a, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht023c, ht024b, ht123b, hbg1c, hbg0a]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht023b, ht034b, ht024c]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht023b, ht034b, ht134a, ht024c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb1 := m.budget 1 (by decide) 0 4 2 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        have hb0 := m.budget 0 (by decide) 1 4 2 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc42, hc40, hc41] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, h231, h340, ht012c, ht024a, ht123a, hbg4]
                            ·
                              linarith only [hdelta1, ht012c, ht123a, hbg4, ht234e, ht024c]
                            ·
                              linarith only [hn, hdelta1, h010, h231, ht123a, hbg4, ht124c, hbg0]
                            ·
                              linarith only [hn, hdelta1, ht013d, ht014c, hbg4, hbg0, hbg3]
                            ·
                              linarith only [hdelta1, h231, h340, ht012c, ht123a, ht024c, hbg4c]
                            ·
                              linarith only [hdelta1, h010, h231, ht123a, ht124c, hbg0, hbg4b]
                            ·
                              linarith only [hdelta1, ht013d, ht014c, hbg0, hbg3, hbg4b]
                            ·
                              linarith only [hdelta1, h010, h141, hbg0, hbg4b]
                            ·
                              linarith only [hdelta1, ht013d, ht014c, hbg0, hbg3, hbg4b]
                            ·
                              linarith only [hdelta1, ht013d, hbg0, hbg3, hbg4a, hbg4b]
                          ·
                            linarith only [hn, hdelta1, h010, h231, ht023b, ht123c, hbg0, ht024c, hbg3]
                          ·
                            linarith only [hn, hdelta1, h010, h231, ht013c, ht023b, hbg0, ht024c, hbg3]
                          ·
                            linarith only [hdelta1, ht013d, ht023a, ht034a, hbg0, ht024c, hbg3]
                          ·
                            linarith only [hdelta1, h010, h131, ht023b, hbg0, ht024c, hbg3b]
                          ·
                            linarith only [hdelta1, h010, h231, ht013c, ht023b, hbg0, ht024c, hbg3b]
                          ·
                            linarith only [hdelta1, ht012c, ht013d, ht123a, hbg0, ht024c, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h131, ht023b, hbg0, ht024c, hbg3a]
                          ·
                            linarith only [hdelta1, h010, h131, ht023b, hbg0, ht024c, hbg3a]
                          ·
                            linarith only [hdelta1, h010, h231, ht013c, ht023b, hbg0, ht024c, hbg3a]
                        ·
                          linarith only [hdelta1, ht012c, ht024b, ht123a, ht234e, hbg0]
                        ·
                          linarith only [hdelta1, ht023c, ht024a, ht234e, hbg0]
                        ·
                          linarith only [hdelta1, ht023b, ht024a, ht123a, hbg1, ht124c, ht234e, hbg0]
                        ·
                          linarith only [hdelta1, h010, h231, ht012c, ht123a, hbg0c]
                        ·
                          linarith only [hdelta1, ht013d, ht024c, hbg0c]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc42, hc40, hc41] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht012c, ht024a, ht123a, hbg4]
                          ·
                            linarith only [hdelta1, h231, h240, ht023b, ht123a, hbg1, ht124c, ht024c, hbg4, hbg0b]
                          ·
                            linarith only [hdelta1, h010, h231, ht123a, ht124c, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, ht023b, ht024a, hbg1, ht234b, hbg4, hbg0b]
                          ·
                            linarith only [hdelta1, h231, h340, ht023b, ht123a, hbg1, ht124c, hbg4c, ht024c, hbg0b]
                          ·
                            linarith only [hdelta1, h231, h340, ht024b, ht123a, ht124c, hbg4c]
                          ·
                            linarith only [hdelta1, ht023b, ht024a, hbg1, hbg4c, hbg0b]
                          ·
                            linarith only [hdelta1, h231, h240, ht123a, ht124c, hbg4c]
                          ·
                            linarith only [hdelta1, ht023b, hbg1, hbg4c, ht024c, ht234b, hbg0b]
                          ·
                            linarith only [hdelta1, ht023b, ht024a, hbg4c, ht234b, hbg0c]
                        ·
                          linarith only [hdelta1, h040, h231, ht013d, ht123a, hbg1, ht124c, hbg0c]
                        ·
                          linarith only [hdelta1, ht023b, ht024b, ht123a, hbg1, ht124c, ht234e, hbg0c]
                        ·
                          linarith only [hdelta1, ht024a, ht123a, hbg1, ht124c, ht234e, hbg0c]
                      ·
                        linarith only [hdelta1, h010, h231, ht014a, ht123a, hbg1]
                      ·
                        linarith only [hdelta1, ht012c, ht024a, ht123c, hbg1, ht234e]
                      ·
                        have hb0 := m.budget 0 (by decide) 1 4 2 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hn, hdelta1, ht014c, ht123b, hbg1, ht124c, hbg0]
                        ·
                          linarith only [hn, hdelta1, ht013c, ht014b, ht023b, hbg1, hbg0]
                        ·
                          linarith only [hdelta1, ht012a, h231, h340, ht013c, ht024a, ht123a, hbg1, hbg0, ht234b]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc42, hc40, hc41] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, h231, h340, ht023a, ht024a, hbg4]
                            ·
                              linarith only [hdelta1, ht012c, ht123a, ht234e, ht024c, hbg4]
                            ·
                              linarith only [hdelta1, ht013c, ht014b, ht023b, ht024a, ht123a, hbg1, ht124c, ht234e, hbg4]
                            ·
                              linarith only [hn, hdelta1, ht013c, ht014a, hbg1, hbg3, hbg4]
                            ·
                              linarith only [hdelta1, h231, h340, ht012c, ht123a, hbg4c, ht024c]
                            ·
                              linarith only [hdelta1, ht014b, ht123b, hbg1, ht124c, hbg4b]
                            ·
                              linarith only [hdelta1, ht013c, ht014a, hbg1, hbg3, hbg4b]
                            ·
                              linarith only [hdelta1, ht014b, ht123b, hbg1, ht124c, hbg4b]
                            ·
                              linarith only [hdelta1, ht013c, ht014a, hbg1, hbg3, hbg4b]
                            ·
                              linarith only [hdelta1, ht013c, ht014a, hbg1, hbg3, hbg4b]
                          ·
                            linarith only [hn, hdelta1, ht013b, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht013c, ht023b, ht024a, hbg3, ht234e]
                          ·
                            linarith only [hdelta1, ht023a, ht024a, hbg3, ht234b]
                          ·
                            linarith only [hdelta1, ht013b, hbg1, hbg3b]
                          ·
                            have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc42, hc40, hc41] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, h231, h340, ht012c, ht024a, ht123b, hbg4, hbg3b]
                            ·
                              linarith only [hdelta1, h231, h240, ht014c, ht123b, ht124c, hbg4, hbg3b]
                            ·
                              linarith only [hdelta1, h040, h231, ht123b, ht124c, hbg4, hbg3b]
                            ·
                              linarith only [hdelta1, ht013c, ht014a, hbg1, hbg3a, hbg4]
                            ·
                              linarith only [hdelta1, h231, h340, ht012c, ht123b, hbg4c, ht024c, hbg3b]
                            ·
                              linarith only [hdelta1, ht014b, ht123b, hbg1, ht124c, hbg4b]
                            ·
                              linarith only [hdelta1, ht012c, ht014a, ht024a, ht123b, hbg1, hbg4c]
                            ·
                              linarith only [hdelta1, ht014b, ht123b, hbg1, ht124c, hbg4b]
                            ·
                              linarith only [hdelta1, ht013c, ht014c, hbg3c, ht234e, hbg4c]
                            ·
                              linarith only [hdelta1, ht014b, ht123b, hbg1, ht124c, hbg4a]
                          ·
                            linarith only [hdelta1, ht013c, ht014a, ht123a, hbg1, ht124c, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht012c, ht024a, ht123b, hbg3c, ht234b]
                        ·
                          linarith only [hdelta1, ht012c, ht123b, hbg0b, hbg1, hbg0a]
                        ·
                          linarith only [hdelta1, ht012b, ht013c, hbg0b, hbg1]
                        ·
                          linarith only [hdelta1, ht013c, ht023b, hbg1, hbg0a, ht024c]
                        ·
                          linarith only [hdelta1, ht012b, ht013c, hbg1, hbg0b]
                        ·
                          linarith only [hdelta1, ht013c, ht014b, ht023b, hbg1, hbg0a]
                        ·
                          linarith only [hdelta1, ht012b, ht013c, hbg1, hbg0a]
                      ·
                        linarith only [hdelta1, h010, h231, ht123a, hbg1c]
                      ·
                        have hb0 := m.budget 0 (by decide) 1 4 2 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, h010, h231, ht014c, ht123c, ht124c, hbg0, hbg1b]
                        ·
                          linarith only [hdelta1, h040, h231, ht012c, ht123c, hbg0, hbg1b]
                        ·
                          linarith only [hdelta1, ht013c, ht024a, ht123c, ht234e, hbg0]
                        ·
                          linarith only [hdelta1, ht023b, ht024a, ht123c, ht124c, ht234e, hbg0, hbg1c]
                        ·
                          linarith only [hdelta1, h010, h231, ht012c, ht123c, hbg1b, hbg0c]
                        ·
                          linarith only [hdelta1, ht013d, ht024c, hbg0c]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht012c, ht123c, ht024c, hbg3, hbg1b, hbg0c]
                          ·
                            linarith only [hdelta1, h010, h231, ht023b, ht123c, ht024c, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h231, ht012c, ht024c, hbg3, hbg1b, hbg0a]
                          ·
                            linarith only [hdelta1, ht012c, ht034b, ht123c, ht024c, hbg3, hbg1b]
                          ·
                            have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc42, hc40, hc41] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, h131, h340, ht012c, ht024a, hbg4, hbg1b]
                            ·
                              linarith only [hdelta1, h231, h240, ht012c, ht123c, hbg4, ht024c, hbg1b]
                            ·
                              linarith only [hdelta1, h040, h131, ht124c, hbg4, hbg1b]
                            ·
                              linarith only [hdelta1, h010, h231, ht123c, hbg4, hbg1a, hbg3c]
                            ·
                              linarith only [hdelta1, h231, h340, ht012c, ht123c, ht024c, hbg1b, hbg4c]
                            ·
                              linarith only [hdelta1, h231, h340, ht023b, ht024a, ht123c, ht124c, hbg1b, hbg0c, hbg4c]
                            ·
                              linarith only [hdelta1, h010, h231, ht012c, ht024a, ht123c, hbg1c, hbg4c]
                            ·
                              linarith only [hdelta1, h231, h240, ht123c, ht124c, hbg1b, hbg4c]
                            ·
                              linarith only [hdelta1, ht014c, ht123c, ht234e, hbg3c, hbg4c]
                            ·
                              linarith only [hdelta1, h010, h131, hbg0a, hbg3c, hbg4c]
                          ·
                            linarith only [hdelta1, h010, h231, ht124c, hbg1c, hbg3b]
                          ·
                            linarith only [hdelta1, ht012c, ht123c, ht024c, hbg1b, hbg3c, hbg0c]
                          ·
                            linarith only [hdelta1, h010, h231, ht124c, hbg1c, hbg3b]
                          ·
                            linarith only [hdelta1, ht023b, ht024a, ht123c, hbg3c, ht234b]
                          ·
                            linarith only [hdelta1, h010, h231, ht124c, hbg1c, hbg3a]
                        ·
                          linarith only [hdelta1, ht013d, ht024b, ht123c, hbg0c, ht124c, ht234e, hbg1c]
                        ·
                          linarith only [hdelta1, ht023b, ht024b, ht123c, hbg0c, ht124c, ht234e, hbg1c]
                        ·
                          linarith only [hdelta1, ht024a, ht123c, hbg0c, ht124c, ht234e, hbg1c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc42, hc40, hc41] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht012c, ht024a, ht123a, hbg4]
                          ·
                            linarith only [hdelta1, ht012c, ht123a, ht234e, ht024c, hbg4]
                          ·
                            linarith only [hdelta1, ht024b, ht123a, ht124c, ht234e, hbg4]
                          ·
                            linarith only [hdelta1, ht013c, hbg1b, hbg1a, hbg3, hbg4]
                          ·
                            linarith only [hdelta1, h231, h340, ht012c, ht123a, ht024c, hbg4c]
                          ·
                            linarith only [hdelta1, h231, h340, ht024b, ht123a, ht124c, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, hbg4b, hbg1c, hbg3]
                          ·
                            linarith only [hdelta1, h231, h240, ht123a, ht124c, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, hbg1c, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, ht013c, hbg1c, hbg3, hbg4b]
                        ·
                          linarith only [hdelta1, ht023b, ht024a, ht123c, ht234e, hbg3]
                        ·
                          linarith only [hdelta1, ht013c, ht023b, ht024a, ht234e, hbg3]
                        ·
                          linarith only [hdelta1, ht012c, ht024a, ht123a, ht234b, hbg3]
                        ·
                          linarith only [hdelta1, h231, h340, ht123a, ht124c, hbg1c, hbg3c]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc42, hc40, hc41] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht014c, ht024b, ht123b, ht124c, hbg3b, hbg4]
                          ·
                            linarith only [hdelta1, h231, h240, ht014c, ht123b, ht124c, hbg3b, hbg4]
                          ·
                            linarith only [hdelta1, h040, h231, ht123b, ht124c, hbg3b, hbg4]
                          ·
                            linarith only [hdelta1, ht013c, hbg1c, hbg3a, hbg4]
                          ·
                            linarith only [hdelta1, h231, h340, ht013c, ht023b, ht024c, hbg3b, hbg4c]
                          ·
                            linarith only [hdelta1, h231, h340, ht024b, ht123b, ht124c, hbg3b, hbg4c]
                          ·
                            linarith only [hdelta1, ht012c, ht024a, ht123b, hbg1c, hbg4c]
                          ·
                            linarith only [hdelta1, h231, h240, ht123b, ht124c, hbg3b, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, ht014c, ht234e, hbg3c, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, ht024b, ht234e, hbg3c, hbg4c]
                        ·
                          linarith only [hdelta1, ht013c, ht123a, ht124c, hbg1c, hbg3c]
                        ·
                          linarith only [hdelta1, ht023b, ht024a, ht234e, hbg3c]
                        ·
                          linarith only [hdelta1, ht023b, ht024a, ht123c, ht234b, hbg3c]
                        ·
                          linarith only [hdelta1, ht012c, ht024a, ht123b, ht234b, hbg3c]
                      ·
                        linarith only [hdelta1, h010, h131, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht023a, ht024a, ht123a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht023c, ht034a, ht123b, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023a, ht034b, ht234a, ht024c]
                    ·
                      have hb3 := m.budget 3 (by decide) 4 0 2 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc30, hc32, hc31] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        have hb0 := m.budget 0 (by decide) 1 4 2 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, h010, h121, ht023a, ht123a, hbg0, ht024c]
                        ·
                          linarith only [hdelta1, h040, h121, ht023a, ht123a, hbg0]
                        ·
                          linarith only [hdelta1, ht012e, ht023c, ht123a, hbg0]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hn, hdelta1, ht134d, hbg0, hbg1, hbg3]
                          ·
                            linarith only [hn, hdelta1, h121, h340, ht014a, ht123c, hbg0, hbg1, hbg3]
                          ·
                            linarith only [hn, hdelta1, h121, h340, ht013a, hbg0, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, ht123a, hbg1]
                          ·
                            linarith only [hdelta1, h131, h340, hbg1b, hbg0, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h121, h340, ht013a, hbg1b, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht134d, hbg0, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h131, h340, ht014a, hbg0, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h131, h340, ht014a, hbg0, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h121, h340, ht013a, hbg0, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, h010, h121, ht023a, ht123a, hbg0c]
                        ·
                          linarith only [hdelta1, h010, h121, ht023c, ht123a, hbg0c, ht024c]
                        ·
                          linarith only [hdelta1, h121, h340, ht023a, ht123a, hbg0c, ht024c, hbg3]
                        ·
                          linarith only [hdelta1, h040, h121, ht023c, ht123a, hbg0c]
                        ·
                          linarith only [hdelta1, h121, h340, ht014b, ht023a, ht123a, hbg0c, hbg3]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht024a, hbg1, hbg0c, ht124d]
                          ·
                            linarith only [hdelta1, h121, h340, ht014a, ht024a, hbg1, ht123c, hbg0c, ht234b]
                          ·
                            linarith only [hdelta1, h121, h340, ht013a, ht024a, hbg1, hbg0c, ht234b]
                          ·
                            linarith only [hdelta1, ht012b, ht023c, ht123a, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, h121, h240, ht024a, ht123c, hbg0c, hbg1c]
                          ·
                            linarith only [hdelta1, h121, h340, ht023c, ht123b, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, ht023c, ht123a, ht134d, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, h121, h340, ht013c, hbg1b, hbg3]
                          ·
                            linarith only [hdelta1, h131, h340, ht014a, ht023c, ht123a, hbg1c, hbg3]
                          ·
                            linarith only [hdelta1, h121, h340, ht013c, hbg1a, hbg3]
                      ·
                        linarith only [hdelta1, h121, h340, ht023b, ht024a, ht123a, ht234b, hbg3]
                      ·
                        linarith only [hdelta1, h131, h340, ht023a, ht024a, ht234b, hbg3]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht123b, ht234b, hbg3]
                      ·
                        linarith only [hdelta1, h121, h340, ht123a, hbg3c]
                      ·
                        have hb0 := m.budget 0 (by decide) 1 4 2 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, h010, h121, ht023a, ht123c, hbg3b, ht024c, hbg0]
                        ·
                          linarith only [hdelta1, h040, h121, ht023a, ht123c, hbg3b, hbg0]
                        ·
                          linarith only [hdelta1, h020, h121, ht023c, ht123c, hbg3b, hbg0]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht134d, hbg1, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h121, h340, ht014a, ht123c, hbg1, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h020, h121, ht023a, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, ht123c, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, h121, h340, hbg1c, ht123c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h121, h340, ht012b, ht023a, hbg3c, hbg0, hbg1b]
                          ·
                            linarith only [hdelta1, ht023c, ht134d, ht123c, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, h121, h340, ht023c, hbg1b, hbg3c]
                          ·
                            linarith only [hdelta1, ht014a, ht123c, hbg1c]
                          ·
                            linarith only [hdelta1, h121, h340, ht023c, hbg1a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h131, ht023a, hbg3b, hbg0c]
                        ·
                          linarith only [hdelta1, h010, h121, ht023c, ht123c, hbg3b, ht024c, hbg0c]
                        ·
                          linarith only [hdelta1, h121, h340, ht023a, ht123c, ht024c, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, h040, h121, ht023c, ht123c, hbg3b, hbg0c]
                        ·
                          linarith only [hdelta1, h121, h340, ht014b, ht023a, ht123c, hbg3c, hbg0c]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht024a, hbg1, ht124d, hbg0c]
                          ·
                            linarith only [hdelta1, h121, h340, ht014a, ht024a, ht123c, hbg1, ht234b, hbg0c]
                          ·
                            linarith only [hdelta1, h121, h340, ht023c, ht024a, hbg1, hbg3b, ht234b, hbg0a]
                          ·
                            linarith only [hdelta1, ht012b, ht023c, ht123c, hbg1, hbg3b, hbg0a]
                          ·
                            linarith only [hdelta1, h121, h340, ht024a, ht123c, ht234b, hbg0c, hbg1c]
                          ·
                            linarith only [hdelta1, h121, h340, ht023c, hbg1b, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht134d, ht123c, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, h121, h340, ht023c, hbg1b, hbg3c]
                          ·
                            linarith only [hdelta1, ht014a, ht123c, hbg1c]
                          ·
                            linarith only [hdelta1, h121, h340, ht023c, hbg1a, hbg3c]
                      ·
                        have hb0 := m.budget 0 (by decide) 1 4 2 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, h010, h121, ht023a, ht123a, hbg0, ht024c]
                        ·
                          linarith only [hdelta1, h040, h121, ht023a, ht123a, hbg0]
                        ·
                          linarith only [hdelta1, ht013c, ht024a, hbg3b, hbg0, ht234b]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, hbg3b, ht134c, hbg1, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht014a, hbg3b, hbg1, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h121, h340, ht023c, hbg1, ht123b, hbg3a]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, ht123a, hbg1]
                          ·
                            linarith only [hdelta1, hbg0, hbg1b, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, ht134c, hbg0, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, ht134c, hbg0, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, ht014a, hbg0, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, ht014a, hbg0, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, ht014b, ht023a, hbg1c, ht123b, ht024c]
                        ·
                          linarith only [hdelta1, h010, h031, ht023a, ht123b, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h121, ht023c, ht123a, ht024c, hbg0c]
                        ·
                          linarith only [hdelta1, ht023a, ht123b, ht024c, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht023c, ht024b, hbg3b, ht123b, ht234b, hbg0c]
                        ·
                          linarith only [hdelta1, ht014b, ht023a, ht123b, hbg0c, hbg3c]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht024a, ht124d, hbg0c, hbg1]
                          ·
                            linarith only [hdelta1, ht014a, ht024a, hbg3b, ht234b, hbg0c, hbg1]
                          ·
                            linarith only [hdelta1, h020, h121, ht023c, ht123b, hbg0a, hbg1]
                          ·
                            linarith only [hdelta1, ht012b, ht023c, ht123a, hbg0a, hbg1]
                          ·
                            linarith only [hdelta1, ht024a, hbg3b, ht234b, hbg0c, hbg1c]
                          ·
                            linarith only [hdelta1, h121, h340, ht024a, ht134c, ht234b, hbg0c, hbg1c]
                          ·
                            linarith only [hdelta1, ht023c, ht123a, ht134c, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, h121, h340, ht014a, ht024a, ht234b, hbg0c, hbg1c]
                          ·
                            linarith only [hdelta1, ht014a, ht023c, ht123a, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h340, ht023b, ht024a, ht123c, ht234b, hbg3c]
                      ·
                        linarith only [hdelta1, ht023b, ht024a, ht123b, ht234b, hbg3c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht234b, hbg3c]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 0 3 2 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht013c, hbg3, ht124a, ht234d, ht123c]
                        ·
                          linarith only [hdelta1, ht023b, hbg3, ht124a, ht234d, ht123c]
                        ·
                          linarith only [hn, hdelta1, h010, h341, hbg3, hbg1]
                        ·
                          linarith only [hdelta1, h010, h241, ht012c, ht023a, ht134a, hbg3, ht124a, hbg1]
                        ·
                          linarith only [hdelta1, ht124a, ht234d, hbg3c, ht123c]
                        ·
                          linarith only [hdelta1, h010, h341, hbg3b, hbg1]
                        ·
                          linarith only [hdelta1, ht013c, ht234c, ht124a, hbg3c, ht123c]
                        ·
                          linarith only [hdelta1, h010, h341, hbg3b, hbg1]
                        ·
                          linarith only [hdelta1, ht023b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h341, hbg3a, hbg1]
                      ·
                        linarith only [hdelta1, h010, h241, ht013a, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, ht124c, ht234d, hbg1]
                      ·
                        have hb0 := m.budget 0 (by decide) 1 3 2 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hn, hdelta1, ht014c, ht023c, ht024b, hbg0, hbg1]
                        ·
                          linarith only [hn, hdelta1, ht013b, ht014c, ht024b, hbg0, hbg1]
                        ·
                          linarith only [hn, hdelta1, ht012b, ht014c, hbg0, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht013c, hbg3, ht124a, ht234d, ht123c]
                          ·
                            linarith only [hdelta1, ht023b, hbg3, ht124a, ht234d, ht123c]
                          ·
                            have hb4 := m.budget 4 (by decide) 0 1 2 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc40, hc41, hc42, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hn, hdelta1, h040, h341, ht013a, hbg3, hbg4, hbg1]
                            ·
                              linarith only [hdelta1, ht014c, ht023a, ht024b, ht234d, hbg4]
                            ·
                              linarith only [hdelta1, h230, h341, ht023a, ht024a, hbg4]
                            ·
                              linarith only [hn, hdelta1, ht013a, ht014c, hbg3, hbg4, hbg1]
                            ·
                              linarith only [hdelta1, ht012b, ht024b, hbg1, hbg4a]
                            ·
                              linarith only [hdelta1, ht012b, ht024b, hbg1, hbg4a]
                            ·
                              linarith only [hdelta1, ht012b, ht024b, hbg1, hbg4a]
                            ·
                              linarith only [hdelta1, h010, h341, ht014a, hbg4c]
                            ·
                              linarith only [hdelta1, ht013a, ht014c, hbg3, hbg4b, hbg1]
                            ·
                              linarith only [hdelta1, ht013a, ht014c, hbg3, hbg4b, hbg1]
                          ·
                            linarith only [hdelta1, ht013a, ht014c, ht023a, ht024b, ht134a, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, ht013b, ht124b, ht123c, hbg1, hbg3b]
                          ·
                            have hb4 := m.budget 4 (by decide) 0 1 2 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc40, hc41, hc42, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hn, hdelta1, ht014b, hbg4, hbg1]
                            ·
                              linarith only [hdelta1, h230, h241, ht014c, ht023c, ht024b, hbg3a, hbg4]
                            ·
                              linarith only [hdelta1, h230, h341, ht023c, ht024a, hbg3a, hbg4]
                            ·
                              linarith only [hdelta1, ht013a, ht014c, hbg4, hbg1, hbg3b]
                            ·
                              linarith only [hdelta1, ht012b, ht024b, hbg4a, hbg1]
                            ·
                              linarith only [hdelta1, ht012b, ht024b, hbg4a, hbg1]
                            ·
                              linarith only [hdelta1, ht012b, ht024b, hbg4a, hbg1]
                            ·
                              linarith only [hdelta1, h010, h341, ht014a, hbg4c]
                            ·
                              linarith only [hdelta1, ht013c, ht014c, hbg4c, ht234d, hbg3c]
                            ·
                              linarith only [hdelta1, ht012a, ht014c, ht124a, hbg4c, hbg1]
                          ·
                            linarith only [hdelta1, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, ht124b, ht123c, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, ht013b, ht124b, ht123c, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, ht013a, ht014c, ht023a, ht024b, hbg3c, hbg1]
                        ·
                          linarith only [hdelta1, ht014c, ht024b, hbg0a, hbg0b, hbg1]
                        ·
                          linarith only [hdelta1, ht012b, ht014c, hbg0b, hbg1]
                        ·
                          linarith only [hdelta1, ht014c, ht023c, ht024b, hbg0a, hbg1]
                        ·
                          linarith only [hdelta1, ht012b, ht014c, hbg0b, hbg1]
                        ·
                          linarith only [hdelta1, ht013b, ht014c, ht024b, hbg0a, hbg1]
                        ·
                          linarith only [hdelta1, ht012b, ht014c, hbg0a, hbg1]
                      ·
                        linarith only [hdelta1, h010, h341, ht234c, ht124a, hbg1c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht013c, hbg3, ht124c, ht234d, ht123c, hbg1b]
                        ·
                          linarith only [hdelta1, h030, h341, hbg3, ht234c, ht124c, ht123c, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h341, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, ht012c, ht023a, hbg3, ht234c, ht124c, hbg1b]
                        ·
                          linarith only [hdelta1, ht124c, ht234d, ht123c, hbg3c, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h341, ht013c, ht124c, hbg1c, ht234d, ht123c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht234c, ht124c, ht123c, hbg3c, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h341, ht023b, ht124c, hbg1c, ht234d, ht123c, hbg3c]
                        ·
                          linarith only [hdelta1, ht023b, ht234c, ht124c, ht123c, hbg3c, hbg1b]
                        ·
                          linarith only [hdelta1, h010, h141, ht012c, ht023a, hbg1c, hbg3c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht013c, ht124a, hbg3, ht234d, ht123c]
                        ·
                          linarith only [hdelta1, ht013b, hbg1b, hbg3, ht124b, ht123c]
                        ·
                          linarith only [hdelta1, h010, h341, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, ht023a, ht024a, ht234c, hbg3]
                        ·
                          linarith only [hdelta1, h230, h241, ht124a, hbg3c, ht123c]
                        ·
                          have hb4 := m.budget 4 (by decide) 0 1 2 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc40, hc41, hc42, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hn, hdelta1, h230, h341, ht023c, ht024b, hbg1c, hbg4, hbg3c]
                          ·
                            linarith only [hdelta1, ht014c, ht023c, ht024b, ht234d, hbg4, hbg3a]
                          ·
                            linarith only [hdelta1, h230, h341, ht023c, ht024a, hbg4, hbg3a]
                          ·
                            linarith only [hdelta1, ht014c, hbg3b, hbg1c, hbg4]
                          ·
                            linarith only [hdelta1, h230, h341, ht023c, ht024b, hbg4a, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, h230, h341, ht023c, ht024b, hbg4a, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, h230, h341, ht023c, ht024b, hbg4a, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, h010, ht012a, h341, ht124b, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, ht014c, ht234d, hbg3c, hbg4c]
                          ·
                            linarith only [hdelta1, ht014c, ht124a, hbg1c, ht123c, hbg4c]
                        ·
                          linarith only [hdelta1, ht034a, hbg3c]
                        ·
                          have hb4 := m.budget 4 (by decide) 0 1 2 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc40, hc41, hc42, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h230, h241, ht023a, ht024b, ht124a, hbg1c, hbg4, ht123c]
                          ·
                            linarith only [hdelta1, h010, h241, ht013b, ht124b, hbg4, ht123c, hbg3a]
                          ·
                            linarith only [hdelta1, h230, h341, ht023a, ht024a, hbg4]
                          ·
                            linarith only [hdelta1, ht014c, hbg1c, hbg4, hbg3b]
                          ·
                            linarith only [hdelta1, h010, h341, ht014b, ht023b, hbg4c, ht234d, hbg3c]
                          ·
                            linarith only [hdelta1, h230, h341, ht023a, ht024b, ht124a, hbg4c, hbg1c, ht123c]
                          ·
                            linarith only [hdelta1, hbg4c, hbg1c, hbg3b]
                          ·
                            linarith only [hdelta1, h010, h341, ht014a, hbg4c]
                          ·
                            linarith only [hdelta1, ht014c, ht023b, hbg4c, ht234d, hbg3c]
                          ·
                            linarith only [hdelta1, ht014c, ht124a, hbg4c, hbg1c, ht123c]
                        ·
                          linarith only [hdelta1, ht023b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht014c, ht023a, ht024b, hbg1c, hbg3c]
                      ·
                        linarith only [hdelta1, h010, h341, ht013a, ht234c, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c, ht124b]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht134c, ht124b, ht123c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb0 := m.budget 0 (by decide) 1 3 2 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        linarith only [hdelta1, h010, h121, ht023c, ht024a, ht124a, hbg0]
                      ·
                        linarith only [hdelta1, h030, h121, ht024a, ht124a, hbg0]
                      ·
                        linarith only [hdelta1, ht012e, ht024c, ht124a, hbg0]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h121, h230, ht023c, ht024a, ht124a, hbg3]
                        ·
                          have hb4 := m.budget 4 (by decide) 0 2 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc40, hc42, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h121, h230, ht023a, ht024b, ht124a, hbg4]
                          ·
                            linarith only [hdelta1, h141, h230, ht023a, ht024a, hbg4]
                          ·
                            linarith only [hdelta1, h230, h341, ht023a, ht024a, hbg4, ht124b]
                          ·
                            linarith only [hn, hdelta1, ht013b, ht134a, hbg4, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, h121, h230, ht023a, ht024b, ht124c, hbg4c]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht134b, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, ht013b, ht134a, hbg3, hbg0, hbg4b]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht134b, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, ht013b, ht134a, hbg3, hbg0, hbg4b]
                          ·
                            linarith only [hdelta1, ht013b, ht134a, hbg3, hbg0, hbg4b]
                        ·
                          have hb4 := m.budget 4 (by decide) 0 2 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc40, hc42, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h121, h230, ht023a, ht024b, ht124a, hbg4]
                          ·
                            linarith only [hdelta1, h141, h230, ht023a, ht024a, hbg4]
                          ·
                            linarith only [hdelta1, h230, h341, ht023a, ht024a, ht124b, hbg4]
                          ·
                            linarith only [hn, hdelta1, ht013a, hbg3, hbg4, hbg0]
                          ·
                            linarith only [hdelta1, h121, h230, ht023a, ht024b, ht124c, hbg4c]
                          ·
                            linarith only [hdelta1, h230, h341, ht023a, ht024b, ht124b, hbg4c]
                          ·
                            linarith only [hdelta1, ht013a, hbg4b, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, h230, h341, ht023a, ht024a, hbg4c]
                          ·
                            linarith only [hdelta1, ht013a, hbg3, hbg0, hbg4b]
                          ·
                            linarith only [hdelta1, ht013a, hbg3, hbg0, hbg4b]
                        ·
                          linarith only [hdelta1, ht023a, ht024a, ht134c, ht124b, hbg3]
                        ·
                          linarith only [hdelta1, h230, h341, ht134a, hbg3c]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 3 4 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hn, hdelta1, h230, h341, ht023c, ht024b, hbg1, hbg3c, hbg0]
                          ·
                            linarith only [hdelta1, h121, h230, ht013c, ht124c, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h121, h230, ht014c, ht023c, ht024b, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, ht012b, ht024a, ht124a, hbg1]
                          ·
                            linarith only [hdelta1, h230, h341, ht023c, ht024b, hbg3c, hbg0, hbg1a]
                          ·
                            linarith only [hdelta1, h230, h341, ht023c, ht024b, hbg3c, hbg0, hbg1a]
                          ·
                            linarith only [hdelta1, h230, h341, ht023c, ht024b, hbg3c, hbg0, hbg1a]
                          ·
                            linarith only [hdelta1, h121, h230, ht013a, ht023c, ht024b, hbg3a, hbg1c, hbg0]
                          ·
                            linarith only [hdelta1, ht013a, ht124c, hbg1c]
                          ·
                            linarith only [hdelta1, h230, h341, ht013a, ht023c, ht024a, ht124b, hbg3c, hbg1c]
                        ·
                          linarith only [hdelta1, ht013c, ht134a, hbg3c]
                        ·
                          have hb4 := m.budget 4 (by decide) 0 2 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc40, hc42, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h121, h230, ht023a, ht024b, ht124a, hbg4]
                          ·
                            linarith only [hdelta1, h141, h230, ht023a, ht024a, hbg4]
                          ·
                            linarith only [hdelta1, h230, h341, ht023a, ht024a, ht124b, hbg4]
                          ·
                            linarith only [hdelta1, ht013b, hbg3b, hbg4, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h121, h230, ht023a, ht024b, ht124c, hbg4c]
                          ·
                            linarith only [hdelta1, h230, h341, ht023a, ht024b, ht124b, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, hbg3c, hbg4b, hbg0]
                          ·
                            linarith only [hdelta1, h230, h341, ht023a, ht024a, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, hbg3c, hbg0, hbg4b]
                          ·
                            linarith only [hdelta1, ht013b, hbg3c, hbg0, hbg4b]
                        ·
                          linarith only [hdelta1, ht023b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht023a, ht024b, hbg3c, hbg0]
                      ·
                        linarith only [hdelta1, h010, h121, ht024a, hbg0c, ht124a]
                      ·
                        linarith only [hdelta1, h010, h121, ht023c, ht024c, hbg0c, ht124a]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h121, h230, ht023c, ht024a, hbg3, ht124a]
                        ·
                          linarith only [hdelta1, h010, h131, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h010, h341, ht013c, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, ht023a, ht024a, hbg3, ht134c, ht124b]
                        ·
                          linarith only [hdelta1, h230, h341, ht134a, hbg3c]
                        ·
                          have hb4 := m.budget 4 (by decide) 0 2 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc40, hc42, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht012e, ht024b, ht124a, hbg4]
                          ·
                            linarith only [hdelta1, h010, h141, ht023c, ht024a, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h341, ht014c, ht023c, ht024b, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, ht013c, hbg0c, hbg4, hbg3b]
                          ·
                            linarith only [hdelta1, h010, h121, ht023c, ht024b, ht124c, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h341, ht023c, ht024b, ht124b, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, h121, h230, ht013c, hbg3c, ht124a, hbg4c]
                          ·
                            linarith only [hdelta1, h010, h341, ht023c, ht024a, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, ht023c, ht024a, hbg0c, ht134c, hbg4c]
                          ·
                            linarith only [hdelta1, ht023c, ht024a, hbg0c, ht124b, hbg4c]
                        ·
                          linarith only [hdelta1, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h341, hbg3c, hbg0a]
                        ·
                          linarith only [hdelta1, ht023a, ht024b, ht134a, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht023a, ht024b, hbg0c, hbg3c]
                      ·
                        linarith only [hdelta1, h010, h121, ht013b, ht024c, hbg0c, ht124a]
                      ·
                        have hb4 := m.budget 4 (by decide) 0 2 1 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc40, hc42, hc41, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h010, h121, ht013b, ht024b, ht124a, hbg0a, hbg4]
                        ·
                          linarith only [hdelta1, h010, h121, ht013b, ht024a, ht124c, hbg0a, hbg4]
                        ·
                          linarith only [hdelta1, h010, h341, ht013b, ht014c, ht024b, hbg0a, hbg4]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h121, h230, ht024a, hbg3, ht124a, hbg0a]
                          ·
                            linarith only [hdelta1, ht013b, ht134a, hbg3, hbg4, hbg0b]
                          ·
                            linarith only [hdelta1, ht013a, hbg3, hbg4, hbg0b]
                          ·
                            linarith only [hdelta1, ht023b, ht034c, ht024b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht123d, hbg3c]
                          ·
                            linarith only [hdelta1, h230, h341, ht013a, ht024b, hbg0c, hbg3c]
                          ·
                            linarith only [hdelta1, ht024a, ht134c, ht124b, hbg0a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, hbg3c, hbg4, hbg0b]
                          ·
                            linarith only [hdelta1, ht023b, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013a, ht023b, ht024b, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h341, ht013b, ht024b, ht134c, hbg0a, hbg4c]
                        ·
                          linarith only [hdelta1, h010, h341, ht013b, ht024b, ht124b, hbg0a, hbg4c]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 3 4 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h010, h121, ht134a, ht124a, hbg1, hbg4c]
                          ·
                            linarith only [hdelta1, h010, h121, ht013a, ht134c, ht124a, hbg1, hbg4c]
                          ·
                            linarith only [hdelta1, h030, h121, ht014c, ht024b, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, ht013b, ht024b, ht124a, hbg1, hbg4a, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h121, ht134c, ht124a, hbg1c, hbg4c]
                          ·
                            linarith only [hdelta1, h010, h121, ht134a, ht124b, hbg1c, hbg4c]
                          ·
                            linarith only [hdelta1, ht134a, ht124a, hbg1c, hbg4c]
                          ·
                            linarith only [hdelta1, h010, h121, ht013a, hbg1c]
                          ·
                            linarith only [hdelta1, ht013a, ht124c, hbg1c]
                          ·
                            linarith only [hdelta1, ht013b, ht024b, ht124b, hbg4a, hbg1c, hbg0a]
                        ·
                          linarith only [hdelta1, h010, h341, ht013b, ht024a, hbg4c, hbg0a]
                        ·
                          linarith only [hdelta1, ht013b, ht024a, hbg0c, ht134c, hbg4c]
                        ·
                          linarith only [hdelta1, ht013b, ht024a, hbg0c, ht124b, hbg4c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h041, h230, ht023c, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h230, h341, ht013b, ht023a, ht134a, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, h230, h341, ht013a, ht023a, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, ht023a, ht034c, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h230, h341, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, h230, h341, ht013a, ht023c, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht023c, ht024c, hbg3c, ht134c, ht124b, hbg0a]
                        ·
                          linarith only [hdelta1, h230, h341, ht013b, ht023a, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht023a, ht134a, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht023a, hbg0c, hbg3c]
                    ·
                      linarith only [ht023a, ht024a, ht234a, ht134c, ht124b]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 0 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc30, hc31] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, h121, h230, ht023c, ht024a, ht124a, hbg3]
                      ·
                        linarith only [hdelta1, ht013e, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht123d, ht234c, hbg3]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht134a, ht234c, hbg3]
                      ·
                        linarith only [hdelta1, ht123d, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023c, ht024a, ht123d, ht234c, hbg3c]
                      ·
                        linarith only [hdelta1, ht023c, ht024a, ht134c, ht124b, hbg3c]
                      ·
                        linarith only [hdelta1, ht013e, hbg3c]
                      ·
                        linarith only [hdelta1, ht023b, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht234c, hbg3c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
            ·
              linarith only [ht023c, ht024b, ht034c]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb0 := m.budget 0 (by decide) 1 3 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc42, hc40, hc41, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht012d, ht013c, ht024c, ht134a, hbg4, ht234e, hbg0]
                        ·
                          linarith only [hn, hdelta1, h010, h141, ht034b, hbg4, hbg0]
                        ·
                          linarith only [hn, hdelta1, h010, h341, ht014c, ht034b, hbg4, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, ht024a, ht034a, hbg4, hbg0]
                        ·
                          linarith only [hdelta1, h010, h141, ht034b, hbg4b, hbg0]
                        ·
                          linarith only [hdelta1, h010, h341, ht014c, ht034b, hbg4b, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, ht013c, ht024c, ht134a, hbg4c, hbg0]
                        ·
                          linarith only [hdelta1, h010, h141, ht034b, hbg4a, hbg0]
                        ·
                          linarith only [hdelta1, h010, h141, ht034b, hbg4a, hbg0]
                        ·
                          linarith only [hdelta1, h010, h341, ht014c, ht034b, hbg4a, hbg0]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 3 4 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc42, hc40, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht024c, ht134a, hbg4, ht234e, hbg1]
                          ·
                            linarith only [hn, hdelta1, h010, h121, ht013b, hbg4, ht124c, hbg0]
                          ·
                            linarith only [hn, hdelta1, h010, h341, ht013b, ht014c, hbg4, hbg0]
                          ·
                            linarith only [hdelta1, ht012d, ht024a, ht134a, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, h010, h141, ht013b, hbg0, hbg4b]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht014c, hbg0, hbg4b]
                          ·
                            linarith only [hdelta1, ht012d, ht024c, ht134a, hbg1, hbg4c]
                          ·
                            linarith only [hdelta1, h010, h341, hbg4b, ht134b, hbg1]
                          ·
                            linarith only [hdelta1, h010, h141, ht013b, hbg0, hbg4a]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht014c, hbg0, hbg4a]
                        ·
                          have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc42, hc40, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht013a, ht024c, ht134c, ht234e, hbg4, hbg1]
                          ·
                            linarith only [hn, hdelta1, h010, h141, ht013b, hbg4, hbg0]
                          ·
                            linarith only [hn, hdelta1, h010, h341, ht013b, ht014c, hbg4, hbg0]
                          ·
                            linarith only [hdelta1, ht012d, ht013a, ht024a, ht134c, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, h010, h141, ht013b, hbg4b, hbg0]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht014c, hbg4b, hbg0]
                          ·
                            linarith only [hdelta1, ht013a, ht014d, ht134c, hbg1, hbg4c]
                          ·
                            linarith only [hdelta1, h010, h341, ht013a, hbg4b, hbg1]
                          ·
                            linarith only [hdelta1, h010, h121, ht013b, ht124c, hbg4a, hbg0]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht014c, hbg4a, hbg0]
                        ·
                          linarith only [hn, hdelta1, h010, h121, ht013b, ht014c, hbg1, hbg0]
                        ·
                          linarith only [hn, hdelta1, ht012c, ht013b, ht024c, hbg1, hbg0]
                        ·
                          have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc42, hc40, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht024c, ht134c, hbg4, ht234e, hbg1c]
                          ·
                            linarith only [hn, hdelta1, h010, h141, ht013b, hbg4, hbg0]
                          ·
                            linarith only [hdelta1, h010, h341, hbg4, hbg1b, hbg1a]
                          ·
                            linarith only [hdelta1, ht012d, ht024a, ht134c, hbg4, hbg1c]
                          ·
                            linarith only [hdelta1, h010, h121, ht013b, ht124c, hbg4b, hbg0]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht014c, hbg4b, hbg0]
                          ·
                            linarith only [hdelta1, ht012d, ht024c, ht134c, hbg4c, hbg1c]
                          ·
                            linarith only [hdelta1, h010, h341, hbg4b, hbg1c]
                          ·
                            linarith only [hdelta1, h010, h121, ht013b, ht124c, hbg4a, hbg0]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht014c, hbg4a, hbg0]
                        ·
                          linarith only [hdelta1, h010, h121, ht013b, ht014c, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, ht012c, ht013b, ht024c, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, h010, h121, ht013b, ht014c, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, ht012c, ht013b, ht024c, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, h010, h121, ht013b, ht014c, hbg0, hbg1a]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hn, hdelta1, h121, h230, ht012c, ht034b, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, ht013b, ht034e, ht134a, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, ht013a, ht024b, hbg3, ht234e, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, ht013a, ht023b, ht034b, ht134a, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, h121, h230, ht012c, ht034b, hbg3a, hbg0]
                        ·
                          linarith only [hdelta1, h121, h230, ht012c, ht034b, hbg3a, hbg0]
                        ·
                          linarith only [hdelta1, h121, h230, ht012c, ht034b, hbg3a, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, ht013b, ht024b, ht234e, hbg0, hbg3c]
                        ·
                          linarith only [hdelta1, ht023b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht012d, ht013a, ht023b, ht034b, hbg0, hbg3c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc42, hc40, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht013a, ht024c, ht134a, hbg4, ht234e, hbg0]
                          ·
                            linarith only [hn, hdelta1, h141, h230, ht034b, hbg4, hbg3]
                          ·
                            linarith only [hn, hdelta1, h230, h341, ht014c, ht034b, hbg4, hbg3]
                          ·
                            linarith only [hdelta1, ht013a, ht024a, ht134a, hbg4, hbg0]
                          ·
                            linarith only [hdelta1, h141, h230, ht034b, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, h230, h341, ht014c, ht034b, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, ht013a, ht024c, ht134a, hbg4c, hbg0]
                          ·
                            linarith only [hdelta1, h230, h341, ht014b, ht023c, hbg4b, hbg3, hbg4a, hbg0]
                          ·
                            linarith only [hdelta1, h141, h230, ht034b, hbg3, hbg4a]
                          ·
                            linarith only [hdelta1, h230, h341, ht014c, ht034b, hbg3, hbg4a]
                        ·
                          linarith only [hdelta1, ht013b, ht024a, ht134a, hbg3, ht234e, hbg0]
                        ·
                          linarith only [hdelta1, ht013a, ht024a, hbg3, ht234e, hbg0]
                        ·
                          linarith only [hdelta1, ht013a, ht023a, ht134a, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, h230, h341, ht134a, hbg3c]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 3 4 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h010, h341, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, h141, h230, ht013c, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h121, h230, ht014a, ht034b, ht024c, hbg1, hbg3a, hbg0]
                          ·
                            have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc42, hc40, hc41, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, h240, h341, ht012c, ht013a, ht024c, hbg1, hbg3b, hbg4]
                            ·
                              linarith only [hdelta1, h141, h230, ht034b, hbg3a, hbg4]
                            ·
                              linarith only [hdelta1, h230, h341, ht014c, ht034b, hbg3a, hbg4]
                            ·
                              linarith only [hdelta1, ht012c, ht013a, ht024a, hbg1, hbg3b, hbg4]
                            ·
                              linarith only [hdelta1, ht013b, ht034b, ht124c, hbg1, hbg4b]
                            ·
                              linarith only [hdelta1, ht014c, hbg4c, ht234e]
                            ·
                              linarith only [hdelta1, ht012c, ht013a, ht024c, hbg4c, hbg1, hbg3b]
                            ·
                              linarith only [hdelta1, ht014b, ht124c, hbg1, hbg4a]
                            ·
                              linarith only [hdelta1, ht014b, ht124c, hbg1, hbg4a]
                            ·
                              linarith only [hdelta1, ht013a, ht024a, ht134b, hbg4c, hbg0]
                          ·
                            linarith only [hdelta1, h230, h341, ht034b, ht024c, hbg1a, hbg3c, hbg0]
                          ·
                            linarith only [hdelta1, h230, h341, ht034b, ht024c, hbg1a, hbg3c, hbg0]
                          ·
                            linarith only [hdelta1, h230, h341, ht034b, ht024c, hbg1a, hbg3c, hbg0]
                          ·
                            linarith only [hdelta1, h010, h121, ht013a, hbg1c]
                          ·
                            linarith only [hdelta1, ht013a, ht124c, hbg1c]
                          ·
                            linarith only [hdelta1, ht014a, hbg1c]
                        ·
                          linarith only [hdelta1, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht024a, hbg3c, ht234e, hbg0]
                        ·
                          linarith only [hdelta1, ht023b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht023a, hbg3c, hbg0]
                      ·
                        linarith only [hdelta1, ht012d, ht024c, hbg0c]
                      ·
                        linarith only [hdelta1, ht012d, ht034b, hbg0c]
                      ·
                        have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc42, hc40, hc41, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht013c, ht024c, ht134a, hbg0c, ht234e, hbg4]
                        ·
                          linarith only [hdelta1, h010, h141, ht034b, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h010, h341, ht014c, ht034b, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, ht024a, ht034a, hbg0c, hbg4]
                        ·
                          linarith only [hdelta1, ht134c, hbg4c, ht234e]
                        ·
                          linarith only [hdelta1, ht014c, hbg4c, ht234e]
                        ·
                          linarith only [hdelta1, ht024c, ht034a, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, h010, h341, ht034b, hbg4c, hbg0a]
                        ·
                          linarith only [hdelta1, ht024a, ht034b, ht134c, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht014c, ht024a, ht034b, hbg0c, hbg4c]
                      ·
                        linarith only [hdelta1, ht012d, ht013b, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h041, h230, hbg3, hbg0a]
                        ·
                          have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc42, hc40, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h240, h341, ht013b, ht024c, ht134a, hbg0b, hbg3, hbg4]
                          ·
                            linarith only [hdelta1, h010, h121, ht013b, ht124c, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht014c, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, ht013b, ht024a, ht134a, hbg0b, hbg3, hbg4]
                          ·
                            linarith only [hdelta1, ht134c, hbg4c, ht234e]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht134b, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, ht013b, ht024c, ht134a, hbg0b, hbg3, hbg4c]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht134b, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, ht013b, ht024a, ht134c, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht134b, hbg3, hbg4a]
                        ·
                          have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc42, hc40, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h240, h341, ht013a, ht024c, hbg0b, hbg3, hbg4]
                          ·
                            linarith only [hdelta1, h010, h141, ht013b, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, ht013b, ht014c, ht024a, hbg0c, ht234e, hbg4]
                          ·
                            linarith only [hdelta1, ht013a, ht024a, hbg0b, hbg3, hbg4]
                          ·
                            linarith only [hdelta1, ht134c, ht234e, hbg4c]
                          ·
                            linarith only [hdelta1, ht014c, ht234e, hbg4c]
                          ·
                            linarith only [hdelta1, ht013a, ht024c, hbg0b, hbg3, hbg4c]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, hbg0a, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, ht024a, ht134c, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, ht014c, ht024a, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht023b, ht034c, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h230, h341, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, h230, h341, ht013a, ht024c, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht014c, ht134c, hbg3c, hbg0a]
                        ·
                          have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc42, hc40, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h240, h341, ht013b, ht024c, hbg0b, hbg4, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h141, ht013b, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht014c, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, ht013b, ht024a, hbg0b, hbg4, hbg3c]
                          ·
                            linarith only [hdelta1, ht134c, hbg4c, ht234e]
                          ·
                            linarith only [hdelta1, ht014c, hbg4c, ht234e]
                          ·
                            linarith only [hdelta1, ht014d, ht013b, hbg3c, hbg4c]
                          ·
                            linarith only [hdelta1, h230, h341, ht013b, ht023a, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, ht024a, ht134c, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, ht014c, ht024a, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht023b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht023b, ht024c, hbg0c, hbg3c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h021, h230, ht034b, hbg0a, hbg3]
                        ·
                          linarith only [hdelta1, ht013b, ht034e, ht134a, hbg0c, hbg3]
                        ·
                          linarith only [hdelta1, ht013a, ht024b, hbg0c, ht234e, hbg3]
                        ·
                          linarith only [hdelta1, ht013a, ht023b, ht034b, ht134a, hbg0c, hbg3]
                        ·
                          linarith only [hdelta1, h230, h341, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, h230, h341, ht013a, ht034b, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht034e, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht023b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht023b, ht034b, hbg0c, hbg3c]
                    ·
                      linarith only [ht014c, ht023b, ht034b, ht134c, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 0 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc30, hc31] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht123d, ht134a, ht034a, hbg3]
                      ·
                        linarith only [hdelta1, ht013e, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht023b, ht123d, ht034a, hbg3]
                      ·
                        linarith only [hdelta1, ht023b, ht134a, ht034a, hbg3]
                      ·
                        linarith only [hdelta1, ht123d, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht123d, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht134a, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013e, hbg3c]
                      ·
                        linarith only [hdelta1, ht023b, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, hbg3c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 4 0 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc30, hc31] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht013c, ht034a, ht123d, hbg3]
                      ·
                        linarith only [hdelta1, ht013c, ht234a, ht123d, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht234a, ht123d, hbg3]
                      ·
                        linarith only [hdelta1, ht013c, ht034a, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht013c, hbg3c, ht123d]
                      ·
                        linarith only [hdelta1, ht034a, hbg3c, ht123d]
                      ·
                        linarith only [hdelta1, ht013c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht234a, hbg3c, ht123d]
                      ·
                        linarith only [hdelta1, ht013c, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht234a, hbg3c]
                    ·
                      have hb0 := m.budget 0 (by decide) 1 4 3 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht012d, ht023a, ht034d, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht013d, ht014c, ht134d, ht234a, hbg3, hbg0]
                        ·
                          linarith only [hn, hdelta1, h010, h121, ht034c, ht123c, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, ht013c, ht023a, ht034c, ht234a, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, ht014c, ht023c, ht134d, hbg3c, hbg0]
                        ·
                          linarith only [hdelta1, h010, h131, ht034c, hbg0, hbg3b]
                        ·
                          linarith only [hdelta1, ht012d, ht013c, ht023a, ht034c, hbg3c, hbg0]
                        ·
                          linarith only [hdelta1, h010, h131, ht034c, hbg3b, hbg0]
                        ·
                          linarith only [hdelta1, ht013c, hbg3c, ht234a]
                        ·
                          linarith only [hdelta1, h010, h131, ht034c, hbg3a, hbg0]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht023a, ht134d, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012d, ht023c, ht134d, hbg1, hbg3, ht234a]
                          ·
                            linarith only [hn, hdelta1, h121, h340, ht123c, ht024b, hbg3, ht234b, hbg0]
                          ·
                            linarith only [hn, hdelta1, ht013c, ht024b, hbg3, ht234b, hbg0]
                          ·
                            linarith only [hdelta1, ht012d, ht023c, ht134d, hbg1, hbg3c]
                          ·
                            linarith only [hdelta1, h121, h340, ht123c, ht024b, hbg3b, ht234b, hbg0]
                          ·
                            linarith only [hdelta1, ht013c, ht024b, hbg3b, ht234b, hbg0]
                          ·
                            linarith only [hdelta1, h131, h340, ht024b, hbg3b, ht234b, hbg0]
                          ·
                            linarith only [hdelta1, ht013c, ht024b, hbg3b, ht234b, hbg0]
                          ·
                            linarith only [hdelta1, h131, h340, ht024b, ht234b, hbg0, hbg3a]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012d, h121, h340, ht014a, ht023a, ht123c, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht013d, ht014a, hbg1, ht123d, hbg3]
                          ·
                            linarith only [hn, hdelta1, h010, h121, ht014b, ht123c, hbg0, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht013c, ht024b, ht234b, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht012d, h121, h340, ht014a, ht023c, ht123c, hbg1, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h121, ht014b, ht123c, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, ht013c, ht024b, hbg3b, ht234b, hbg0]
                          ·
                            linarith only [hdelta1, h040, h131, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, ht013c, ht024b, hbg3b, ht234b, hbg0]
                          ·
                            linarith only [hdelta1, h131, h340, ht024b, ht234b, hbg3a, hbg0]
                        ·
                          linarith only [hn, hdelta1, h121, h340, ht013c, ht024b, hbg1, ht234b, hbg0]
                        ·
                          linarith only [hn, hdelta1, ht012c, ht014b, ht023c, hbg1, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012d, h121, h340, ht023a, ht123c, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht013d, ht123d, hbg3, hbg1c]
                          ·
                            linarith only [hn, hdelta1, h010, h121, ht014b, ht123c, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, h010, h031, ht024b, hbg1b, ht234b, hbg1a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht012d, h121, h340, ht023c, ht123c, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, h040, h121, ht123c, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, h010, h031, ht024b, ht234b, hbg3b, hbg1c, hbg0]
                          ·
                            linarith only [hdelta1, h040, h131, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, ht013c, ht024b, ht234b, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, h040, h121, ht123c, hbg3a, hbg0]
                        ·
                          linarith only [hdelta1, h121, h340, ht013c, ht024b, ht234b, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, ht012c, ht014b, ht023c, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, h121, h340, ht013c, ht024b, ht234b, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, ht012c, ht014b, ht023c, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, h121, h340, ht013c, ht024b, ht234b, hbg1a, hbg0]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, ht012d, ht023b, ht134d, ht234a, hbg1, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, ht013e, ht014a, hbg1, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, h121, h340, ht013a, ht023b, ht234a, hbg1, hbg0]
                        ·
                          linarith only [hn, hdelta1, ht012c, ht013b, hbg1, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, h121, h340, ht023b, ht123c, ht234a, hbg0, hbg1c]
                        ·
                          linarith only [hdelta1, ht012d, h121, h340, ht023b, ht134c, ht234a, hbg0, hbg1c]
                        ·
                          linarith only [hdelta1, ht012c, ht013b, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, h121, h340, ht014a, ht023b, ht234a, hbg1c, hbg0]
                        ·
                          linarith only [hdelta1, ht012c, ht013b, hbg1b, hbg0]
                        ·
                          linarith only [hdelta1, ht012c, ht014b, ht034c, hbg1b, hbg0]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, ht023a, ht134d, hbg1, ht234a, hbg0]
                        ·
                          linarith only [hdelta1, h121, h340, ht014a, ht023a, ht123c, hbg1, ht234a, hbg0]
                        ·
                          linarith only [hdelta1, h121, h340, ht013a, ht023a, hbg1, ht234a, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht014a, ht023a, ht134d, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht013c, ht014a, ht123c, ht134d, hbg1, hbg3, ht234a]
                          ·
                            linarith only [hn, hdelta1, ht013b, ht123c, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012c, ht013a, ht023a, hbg1, hbg3, ht234a]
                          ·
                            linarith only [hdelta1, ht012c, ht014a, ht023c, ht134d, hbg1, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, ht123c, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, ht012c, ht014a, ht023a, ht134c, hbg1, hbg3c]
                          ·
                            linarith only [hdelta1, ht014b, ht034c, ht123c, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, ht013c, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, ht123c, hbg1, hbg3a]
                        ·
                          linarith only [hdelta1, h121, h340, ht023a, ht123c, ht234a, hbg1c, hbg0]
                        ·
                          linarith only [hdelta1, h121, h340, ht023a, ht134c, ht234a, hbg1c, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h121, h340, ht023a, ht123c, ht134c, hbg1a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, h121, h340, ht023c, ht123c, ht134c, ht234a, hbg1a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht013b, ht123c, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, ht023a, ht134c, ht234a, hbg1a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht023c, ht134d, hbg3c, hbg1a, hbg0]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, ht134d, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, ht023a, ht134c, hbg3c, hbg1a, hbg0]
                          ·
                            linarith only [hdelta1, ht123c, ht134d, hbg3c, ht234a, hbg1c]
                          ·
                            linarith only [hdelta1, ht013a, ht023c, hbg3c, ht234a, hbg0]
                          ·
                            linarith only [hdelta1, ht013b, ht023a, hbg3c, ht234a, hbg0]
                        ·
                          linarith only [hdelta1, h121, h340, ht014a, ht023a, ht234a, hbg1c, hbg0]
                        ·
                          linarith only [hdelta1, ht014a, ht123c, hbg1c]
                        ·
                          linarith only [hdelta1, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, ht013d, hbg0c]
                      ·
                        linarith only [hdelta1, ht012d, ht034c, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht014c, ht023a, ht134d, hbg0c, hbg3]
                        ·
                          linarith only [hdelta1, ht014c, ht023c, ht134d, ht234a, hbg0c, hbg3]
                        ·
                          linarith only [hdelta1, h010, h121, ht034c, ht123c, hbg0a, hbg3]
                        ·
                          linarith only [hdelta1, ht013c, ht023a, ht034c, ht234a, hbg0c, hbg3]
                        ·
                          linarith only [hdelta1, ht014c, ht023c, ht134d, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, h121, h340, ht023a, ht034c, ht123c, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht023a, ht034c, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht123d, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, ht023b, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht012d, ht014b, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h141, h340, ht023a, hbg1, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, h131, h340, ht014a, ht023a, hbg1, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, h121, h340, ht013a, ht023a, hbg1, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, ht012c, ht014b, ht023c, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, h121, h340, ht023a, ht123c, hbg1c, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, h121, h340, ht013c, ht023b, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, ht012c, ht023a, ht134d, hbg1c, hbg3]
                          ·
                            linarith only [hdelta1, h121, h340, ht013c, ht023b, hbg1b, hbg3]
                          ·
                            linarith only [hdelta1, ht014a, ht123c, hbg1c]
                          ·
                            linarith only [hdelta1, h121, h340, ht013c, ht014b, ht023a, hbg1a, hbg0c, hbg3]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h141, h340, ht023c, ht234a, hbg1, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, h131, h340, ht014a, ht023c, ht234a, hbg1, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, h121, h340, ht013a, ht023c, ht234a, hbg1, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, ht012c, ht014b, ht023c, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, h121, h340, ht023c, ht123c, ht234a, hbg1c, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, h121, h340, ht013c, ht234a, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, ht134d, ht234a, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, h121, h340, ht013c, ht234a, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, ht014a, ht123c, hbg1c]
                          ·
                            linarith only [hdelta1, h121, h340, ht013c, ht234a, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, h010, h131, ht014b, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, ht013c, ht024b, ht234b, hbg3, hbg0a]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h141, h340, ht023c, hbg1, hbg0b, hbg3c]
                          ·
                            linarith only [hdelta1, h121, h340, ht014a, ht023c, ht123c, hbg1, hbg0b, hbg3c]
                          ·
                            linarith only [hdelta1, h121, h340, ht013a, ht023c, hbg1, hbg0b, hbg3c]
                          ·
                            linarith only [hdelta1, ht012c, ht014b, ht023c, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, h121, h340, ht023c, ht123c, hbg0b, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, h121, h340, ht013c, hbg1b, hbg3c]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, ht134d, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, h121, h340, ht013c, hbg1b, hbg3c]
                          ·
                            linarith only [hdelta1, h131, h340, ht012c, ht014a, ht023c, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, h121, h340, ht013c, hbg1a, hbg3c]
                        ·
                          linarith only [hdelta1, h131, h340, ht014b, ht023a, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht014b, ht023a, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht123d, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, ht014b, ht023a, ht234a, hbg0c, hbg3c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc42, hc40, hc41] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h121, h340, ht012c, ht034c, ht024b, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h121, h240, ht012c, ht034c, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, ht014b, ht023b, ht134d, ht234a, hbg4, hbg0c]
                        ·
                          linarith only [hdelta1, ht014a, ht023b, ht234a, hbg4, hbg0c]
                        ·
                          linarith only [hdelta1, h121, h340, ht012c, ht034c, hbg0a, hbg4c]
                        ·
                          linarith only [hdelta1, ht024b, ht134d, hbg4c]
                        ·
                          linarith only [hdelta1, ht014a, ht034c, ht024b, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht124d, hbg4c]
                        ·
                          linarith only [hdelta1, ht014a, ht034c, hbg0c, ht234b, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, ht034a, hbg0c, hbg4c]
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            linarith only [ht012b, ht014c, ht024b]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht012b, ht014c, ht034b, ht023b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht012a, ht014c, ht034b, ht123b, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht012a, ht014a, ht123a, ht234a, ht134b]
                    ·
                      have hb1 := m.budget 1 (by decide) 4 0 2 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012a, h140, h231, ht123a, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht123a, ht124b, ht234e, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, h131, h340, ht014a, ht124b, ht234b, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht123a, ht124b, hbg1c, ht234e]
                      ·
                        linarith only [hdelta1, ht012a, ht124b, hbg1c, ht234e, ht123c]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, h231, h340, ht014a, ht124b, hbg1c, ht123c, ht234b]
                      ·
                        linarith only [hdelta1, ht014a, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht024a, ht023a, ht123a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht012b, ht014a, ht023a, ht134b, ht234a]
                    ·
                      have hb1 := m.budget 1 (by decide) 4 0 3 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012b, ht023a, ht123a, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht123c, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht012b, ht014a, ht023a, ht123a, hbg1]
                      ·
                        linarith only [hdelta1, ht123c, ht124e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012b, ht023a, ht124e, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h140, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012b, ht014a, ht023a, ht123b, hbg1c]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            linarith only [ht012b, ht014c, ht024b]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht013b, ht014c, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht013a, ht014c, ht124a, ht123c, ht024b]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 4 0 3 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht013a, ht234a, ht123d, ht134b, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht234a, ht123d, ht134b, hbg1]
                      ·
                        linarith only [hdelta1, h121, h140, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht234a, ht123d, ht134b, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h230, ht013a, ht234a, ht134b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h230, ht014a, ht234a, ht134b, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123c, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1c]
                    ·
                      have hb1 := m.budget 1 (by decide) 4 0 3 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht013a, ht123c, hbg1, ht124e]
                      ·
                        linarith only [hdelta1, ht014a, ht123c, hbg1, ht124e]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1, ht124e]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht123c, hbg1c, ht124e]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c, ht124e]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h340, ht014a, ht124b, ht234b, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123c, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1c]
    ·
      rcases m.triangle 0 1 4 (by decide) (by decide) with ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩ | ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          linarith only [ht012b, ht013c, ht023b]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht123a, ht023a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 0 2 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012a, h230, h241, ht123b, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123b, ht124a, ht234d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, ht123b, ht124c, ht234d, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht123b, ht124a, hbg1c, ht234d]
                      ·
                        linarith only [hdelta1, ht012a, ht123b, ht124c, hbg1c, ht234d]
                      ·
                        linarith only [hdelta1, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, h230, h341, ht013a, ht123b, ht234c, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1c]
                    ·
                      linarith only [ht013b, ht123b, ht034a, ht234a]
                  ·
                    linarith only [ht013a, ht014b, ht034c, ht134a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 0 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h121, h230, ht012b, ht024a, ht123b, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123e, ht124c, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, ht012b, ht013a, ht024a, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, hbg1c, ht123e, ht124c]
                      ·
                        linarith only [hdelta1, ht014a, hbg1c, ht123e]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h130, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c, ht124c]
                      ·
                        linarith only [hdelta1, ht012b, ht013a, ht024a, hbg1c, ht124b]
                    ·
                      linarith only [ht013b, ht123b, ht034a, ht234a]
                  ·
                    linarith only [ht012b, ht013a, ht134a, ht034c, ht024b]
            ·
              linarith only [ht012b, ht013c, ht034c, ht024b]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht123a, ht023a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 0 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123e, hbg1, ht124c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1]
                      ·
                        linarith only [hdelta1, ht123e, hbg1c, ht124c]
                      ·
                        linarith only [hdelta1, ht014a, ht123e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h230, ht013a, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c, ht124c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1c]
                    ·
                      linarith only [ht013b, ht123b, ht034a, ht234a]
                  ·
                    linarith only [ht013a, ht014b, ht034c, ht134a]
            ·
              linarith only [ht014b, ht013c, ht034c]
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          linarith only [ht012b, ht013c, ht023b]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            linarith only [ht012b, ht014c, ht024b]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012a, ht013c, ht123a, ht023b]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 4 0 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012a, h121, h230, ht014a, hbg1, ht123b]
                      ·
                        linarith only [hdelta1, ht012a, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1, ht134b]
                      ·
                        linarith only [hdelta1, ht012a, ht123e, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, ht124e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c, ht134b]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c]
                    ·
                      linarith only [ht034a, ht023b, ht234a]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht123a, ht023a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 4 0 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012a, ht014a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht034a, ht013c, ht134a, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c, ht123e]
                      ·
                        linarith only [hdelta1, ht034a, ht013c, ht134c, hbg1c, ht123e]
                      ·
                        linarith only [hdelta1, ht012a, ht034a, ht013c, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, hbg1c, ht124e]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c, ht134b]
                      ·
                        linarith only [hdelta1, ht034a, ht013c, ht134a, hbg1c]
                    ·
                      linarith only [ht123b, ht134a, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 4 3 0 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012a, h121, h140, ht013a, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, h121, h230, ht134a, hbg1, ht234a]
                      ·
                        linarith only [hdelta1, h121, h230, ht013a, ht134a, hbg1, ht234a]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, h121, h230, ht134b, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h230, ht013a, ht134b, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, ht123e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht134c, hbg1c]
                    ·
                      have hb1 := m.budget 1 (by decide) 4 3 0 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012a, ht013a, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, h121, h340, ht123b, hbg1, ht234a]
                      ·
                        linarith only [hdelta1, h121, h340, ht013a, ht123b, hbg1, ht234a]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1, ht134c]
                      ·
                        linarith only [hdelta1, ht012a, ht124e, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, ht123e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht134c, hbg1c]
  ·
    rcases m.triangle 0 1 3 (by decide) (by decide) with ⟨ht013a,ht013b,ht013c,ht013d,ht013e⟩ | ⟨ht013a,ht013b,ht013c,ht013d,ht013e⟩
    ·
      rcases m.triangle 0 1 4 (by decide) (by decide) with ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩ | ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 2 0 3 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht013a, hbg1, ht123d]
                      ·
                        linarith only [hdelta1, h120, h341, ht012a, ht234a, hbg1, ht123c]
                      ·
                        linarith only [hdelta1, h120, h141, ht012a, ht013a, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, h120, h341, hbg1c, ht234a, ht123c]
                      ·
                        linarith only [hdelta1, ht013a, ht124d, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, h120, h341, ht012a, hbg1c, ht234c, ht124c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c, ht134b]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1c]
                    ·
                      have hb1 := m.budget 1 (by decide) 2 0 3 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h120, h341, ht013a, hbg1, ht134a]
                      ·
                        linarith only [hdelta1, h120, h231, ht012a, hbg1, ht234a, ht134a]
                      ·
                        linarith only [hdelta1, h120, h231, ht012a, ht013a, hbg1, ht234a, ht134c]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, h120, h231, ht234a, ht134a, hbg1c]
                      ·
                        linarith only [hdelta1, h120, h231, ht013a, ht234a, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, h010, h231, ht234a, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht134b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht234a, ht134a, ht123c]
                    ·
                      have hb1 := m.budget 1 (by decide) 2 0 4 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht013a, hbg1, ht123d]
                      ·
                        linarith only [hdelta1, ht012a, ht124d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1, ht123d]
                      ·
                        linarith only [hdelta1, ht012a, ht013b, ht034a, hbg1, ht134a]
                      ·
                        linarith only [hdelta1, ht124d, hbg1c]
                      ·
                        linarith only [hdelta1, ht013b, ht034a, ht134b, hbg1c, ht123d]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, h120, h131, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c, ht134c]
                      ·
                        linarith only [hdelta1, ht012a, ht013b, ht034a, ht134b, hbg1c]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013c, ht123c, ht234a, ht034a]
                    ·
                      have hb1 := m.budget 1 (by decide) 2 0 4 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht013a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht124d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1]
                      ·
                        linarith only [hdelta1, ht123d, hbg1c, ht134c]
                      ·
                        linarith only [hdelta1, ht014a, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, h120, h231, ht012a, ht123c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c, ht134c]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1c]
                ·
                  linarith only [ht012a, ht014b, ht024c, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
          ·
            linarith only [ht012c, ht014b, ht024c]
        ·
          linarith only [ht012c, ht013b, ht023c]
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht013b, ht014c, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht134a, ht034a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013a, ht014a, ht123c, ht234a, ht134b]
                    ·
                      have hb1 := m.budget 1 (by decide) 2 4 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h120, h131, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123d, ht124b, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, ht123d, ht124b, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht012c, ht013b, ht024c, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht012c, ht013a, ht024a, ht134b, ht124c, ht234a, ht123c]
                    ·
                      have hb1 := m.budget 1 (by decide) 2 4 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht124b, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht012c, ht013a, ht024a, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht124b, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012c, ht024a, ht124a, hbg1c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013a, ht014a, ht234a, ht134b, ht123c]
                    ·
                      have hb1 := m.budget 1 (by decide) 4 2 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h131, h140, ht012a, ht013a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, hbg1, ht124a, ht234e, ht123c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1, ht124a, ht234e, ht123c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c, ht234e, ht124b, ht123c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c, ht234e, ht124b, ht123c]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht124c, hbg1c]
              ·
                linarith only [ht012b, ht023a, ht123a]
        ·
          linarith only [ht012c, ht013b, ht023c]
    ·
      rcases m.triangle 0 1 4 (by decide) (by decide) with ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩ | ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 2 3 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h120, h141, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht123b, hbg1, ht124d]
                      ·
                        linarith only [hdelta1, ht012a, hbg1, ht124d]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht123b, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, hbg1c, ht124d]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c, ht124d]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, ht123b, hbg1c, ht124d]
                      ·
                        linarith only [hdelta1, ht014a, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                    ·
                      have hb1 := m.budget 1 (by decide) 2 3 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h120, h141, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht123e, hbg1, ht134c, ht234a]
                      ·
                        linarith only [hdelta1, ht013a, ht123e, hbg1, ht134c, ht234a]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, h120, h231, ht014a, ht134c, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, h120, h231, ht013a, ht134c, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, h130, h231, ht134c, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                  ·
                    linarith only [ht013a, ht014b, ht034c, ht134a]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
            ·
              linarith only [ht013c, ht014b, ht034c]
          ·
            linarith only [ht012c, ht024c, ht014b]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 2 3 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h120, h141, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht124d, ht123b, hbg1]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, ht123a, ht124d, hbg1]
                      ·
                        linarith only [hdelta1, ht012c, ht014a, ht023a, ht123a, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht124d, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124d, hbg1c]
                      ·
                        linarith only [hdelta1, ht012c, ht014a, ht023a, hbg1c, ht123c]
                      ·
                        linarith only [hdelta1, ht124d, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, ht123a, hbg1c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht012c, ht014b, ht023a, ht034c, ht134a, ht123c]
                ·
                  linarith only [ht024a, ht023a, ht123a, ht124a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 2 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h141, h230, ht012a, ht014a, hbg1, ht123b]
                      ·
                        linarith only [hdelta1, ht014a, ht123a, ht124c, hbg1, ht234d]
                      ·
                        linarith only [hdelta1, ht012a, ht123a, ht124c, hbg1, ht234d]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht124c, hbg1c, ht234d, ht123b]
                      ·
                        linarith only [hdelta1, ht012a, ht124c, hbg1c, ht234d, ht123b]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, h230, h341, ht123a, ht124c, ht234c, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht123c, hbg1c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht013a, ht014b, ht034c, ht134a]
                ·
                  linarith only [ht012b, ht024a, ht124a]
            ·
              linarith only [ht012c, ht014b, ht034c, ht023c]
          ·
            linarith only [ht012c, ht014b, ht024c]
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb0 := m.budget 0 (by decide) 2 3 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, h120, h341, ht012e, ht013a, ht034a, hbg0, hbg1]
                        ·
                          linarith only [hdelta1, h130, h341, ht012e, ht014a, ht023c, hbg0, hbg1, ht234a]
                        ·
                          linarith only [hdelta1, ht012e, ht023c, hbg0, ht134e, hbg1, ht234a]
                        ·
                          linarith only [hn, hdelta1, ht012b, ht013c, hbg0, hbg1]
                        ·
                          linarith only [hdelta1, h120, h341, ht012e, ht014a, ht023c, hbg0, ht234a, hbg1c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012e, ht023c, hbg0, ht134b, ht234a, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht013c, hbg0, hbg1b]
                        ·
                          linarith only [hdelta1, h120, h341, ht012e, ht023c, ht123b, hbg0, ht234a, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht013c, hbg0, hbg1b]
                        ·
                          linarith only [hdelta1, ht012b, ht014c, hbg0, ht034b, hbg1b]
                      ·
                        have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hn, hdelta1, h041, h120, ht013b, hbg0, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h041, h120, ht123b, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, h120, h341, ht013e, ht014a, ht123b, hbg3, ht234a, hbg1]
                          ·
                            linarith only [hdelta1, h120, h341, ht012e, ht014a, ht023a, ht123b, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, ht012e, ht014a, ht024a, hbg3, ht234c, hbg1]
                          ·
                            linarith only [hdelta1, h041, h120, ht123b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h041, h120, ht123b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h041, h120, ht123b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h120, h341, ht013e, ht014a, ht123b, hbg3c, hbg1]
                          ·
                            linarith only [hdelta1, ht014b, ht024c, ht234c, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, ht012e, ht014a, ht023b, hbg0, ht024c, ht234c, hbg1, hbg3b]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h120, h341, ht123b, hbg0, ht024c, ht234c, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht023b, ht134e, ht234a, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht023a, ht134e, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht023a, ht134b, ht234a, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, h120, h341, ht123b, hbg0, ht024c, ht234c, hbg3a]
                          ·
                            linarith only [hdelta1, h120, h341, ht123b, hbg0, ht024c, ht234c, hbg3a]
                          ·
                            linarith only [hdelta1, h120, h341, ht123b, hbg0, ht024c, ht234c, hbg3a]
                          ·
                            linarith only [hdelta1, ht012e, ht023b, ht134e, hbg1, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, hbg0, ht024c, ht234c, hbg3b]
                          ·
                            linarith only [hdelta1, ht013b, hbg0, ht024c, ht234c, hbg3b]
                        ·
                          linarith only [hn, hdelta1, ht012b, ht014c, ht023b, hbg0, hbg1]
                        ·
                          linarith only [hdelta1, h120, h341, ht013b, hbg0, ht024c, ht234c, hbg1a]
                        ·
                          linarith only [hdelta1, h120, h341, ht013b, hbg0, ht024c, ht234c, hbg1a]
                        ·
                          linarith only [hdelta1, h120, h341, ht013b, hbg0, ht024c, ht234c, hbg1a]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h041, h120, ht123b, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, h120, h341, ht012e, ht023b, ht123b, ht234a, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, h120, h341, ht012e, ht023a, ht123b, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht012e, ht024a, ht234c, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, h041, h120, ht123b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h041, h120, ht123b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h041, h120, ht123b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h120, h341, ht012e, ht023b, ht123b, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, ht012e, ht023b, hbg0, ht024c, ht234c, hbg3b, hbg1c]
                          ·
                            linarith only [hdelta1, ht012e, ht023b, hbg0, ht024c, ht234c, hbg3b, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht014c, ht023b, hbg0, hbg1b]
                        ·
                          linarith only [hdelta1, ht012b, ht014c, ht023b, hbg0, hbg1b]
                      ·
                        have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hn, hdelta1, h011, h120, ht123b, hbg0, ht034b, hbg3]
                        ·
                          linarith only [hdelta1, ht012e, ht023b, ht034e, hbg0, ht234a, hbg3]
                        ·
                          linarith only [hdelta1, ht012e, ht014b, ht023a, hbg0, ht134e, hbg3]
                        ·
                          linarith only [hdelta1, ht012e, ht013b, ht023a, hbg0, ht034b, ht234a, hbg3]
                        ·
                          linarith only [hdelta1, h011, h130, hbg0, ht034b, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h130, hbg0, ht034b, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h130, hbg0, ht034b, hbg3a]
                        ·
                          linarith only [hdelta1, ht012e, ht014b, ht023b, hbg0, ht134e, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, ht012e, ht013b, ht023a, hbg0, ht034b, hbg3c]
                      ·
                        have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, h120, h341, ht014a, ht023a, hbg0, hbg1, ht134b, ht234a]
                        ·
                          linarith only [hdelta1, h130, h341, ht014a, ht023a, hbg0, hbg1, ht234a]
                        ·
                          linarith only [hdelta1, ht023a, hbg0, ht134e, hbg1, ht234a]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht014c, ht123b, ht034b, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012b, ht014a, ht023b, ht134e, hbg1, ht234a, hbg3]
                          ·
                            linarith only [hdelta1, ht012b, ht014a, ht023a, ht134e, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012b, ht013a, ht023a, hbg1, ht234a, hbg3]
                          ·
                            linarith only [hdelta1, ht013c, ht123b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht013c, ht123b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht013c, ht123b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht012b, ht014a, ht023b, ht134e, hbg1, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, ht012b, ht013a, ht023a, hbg1, hbg3c]
                        ·
                          linarith only [hdelta1, h011, h120, ht014a, hbg1c]
                        ·
                          linarith only [hdelta1, h120, h341, ht023a, hbg0, ht134b, ht234a, hbg1c]
                        ·
                          linarith only [hdelta1, ht013a, hbg1c]
                        ·
                          linarith only [hdelta1, h130, h341, ht023a, hbg0, ht234a, hbg1c]
                        ·
                          linarith only [hdelta1, ht014a, ht123b, hbg1c]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht013c, ht123b, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, ht023b, ht123e, hbg0, hbg1a, ht134b, hbg3]
                          ·
                            linarith only [hdelta1, ht023a, hbg0, ht134e, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, ht023b, ht034a, hbg0, hbg1a, ht134b, hbg3]
                          ·
                            linarith only [hdelta1, ht123b, ht134e, ht234a, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht123b, ht134e, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, h140, h341, ht023b, hbg0, hbg1a, hbg3c]
                          ·
                            linarith only [hdelta1, ht023b, hbg0, hbg1a, ht134b, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, ht023a, hbg0, hbg1a, ht134b, hbg3c]
                      ·
                        linarith only [hdelta1, ht012e, ht014c, hbg0c]
                      ·
                        linarith only [hdelta1, ht012e, ht034b, hbg0c]
                      ·
                        have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc41, hc40, hc42, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht014c, ht034a, ht134e, hbg4, hbg0c]
                        ·
                          linarith only [hdelta1, h020, h241, ht034b, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, ht024c, ht034b, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, ht014a, ht034a, hbg4, hbg0c]
                        ·
                          linarith only [hdelta1, ht134e, hbg4c, ht234c]
                        ·
                          linarith only [hdelta1, ht024c, ht134e, hbg4c]
                        ·
                          linarith only [hdelta1, ht014c, ht034a, hbg4c, hbg0c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, ht034b, hbg4c, hbg0a]
                        ·
                          linarith only [hdelta1, ht014a, ht034b, hbg4c, ht234c, hbg0c]
                        ·
                          linarith only [hdelta1, ht014a, ht024c, ht034b, hbg4c, hbg0c]
                      ·
                        linarith only [hdelta1, ht012e, ht023b, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h041, h120, ht123b, hbg3, hbg0a]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h120, h231, ht013a, ht023b, hbg3, hbg0b, hbg1]
                          ·
                            linarith only [hdelta1, h130, h341, ht014a, ht023b, ht234a, hbg3, hbg0b, hbg1]
                          ·
                            linarith only [hdelta1, h140, h341, ht023b, ht234a, hbg3, hbg0b, hbg1]
                          ·
                            linarith only [hdelta1, ht012b, ht014c, ht023b, hbg0a, hbg1]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, ht234a, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, ht234a, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, ht234a, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h231, ht023b, ht123b, hbg3, hbg1c, hbg0b]
                          ·
                            linarith only [hdelta1, ht014a, ht123b, hbg1c]
                          ·
                            linarith only [hdelta1, ht012b, ht023b, ht134e, ht234a, hbg3, hbg1c]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h120, h341, ht013a, ht023a, hbg3, hbg0b, hbg1]
                          ·
                            linarith only [hdelta1, h130, h341, ht014a, ht023a, hbg3, hbg0b, hbg1]
                          ·
                            linarith only [hdelta1, h140, h341, ht023a, hbg3, hbg0b, hbg1]
                          ·
                            linarith only [hdelta1, ht012b, ht014c, ht023b, hbg0a, hbg1]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, ht023c, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, ht023c, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, ht023c, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, h120, h341, ht023a, ht123b, hbg3, hbg1c, hbg0b]
                          ·
                            linarith only [hdelta1, ht014a, ht123b, hbg1c]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, ht134e, hbg3, hbg1c]
                        ·
                          linarith only [hdelta1, ht013b, ht034c, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, ht123e, hbg3c]
                        ·
                          linarith only [hdelta1, h120, h341, ht014c, ht023a, ht123b, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, ht024c, ht234c, hbg3c, hbg0a]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h120, h341, ht013a, ht023b, hbg3c, hbg1, hbg0b]
                          ·
                            linarith only [hdelta1, h130, h341, ht014a, ht023b, hbg3c, hbg1, hbg0b]
                          ·
                            linarith only [hdelta1, h140, h341, ht023b, hbg3c, hbg1, hbg0b]
                          ·
                            linarith only [hdelta1, ht012b, ht014c, ht023b, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht023b, ht123b, hbg1c, hbg3c, hbg0b]
                          ·
                            linarith only [hdelta1, ht014a, ht123b, hbg1c]
                          ·
                            linarith only [hdelta1, ht012b, ht023b, ht134e, hbg1c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, hbg3c, ht234a]
                        ·
                          linarith only [hdelta1, ht013b, ht014c, ht023a, hbg3c, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h120, ht123b, ht034b, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, ht014b, ht023b, ht134e, ht234a, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, ht014b, ht023a, ht134e, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, ht013b, ht023a, ht034b, ht234a, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, h130, h341, hbg3c, ht234a]
                        ·
                          linarith only [hdelta1, h120, h341, ht023a, ht123b, ht034b, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, ht014b, ht023b, ht134e, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, ht013b, hbg3c, ht234a]
                        ·
                          linarith only [hdelta1, ht013b, ht023a, ht034b, hbg3c, hbg0c]
                    ·
                      have hb3 := m.budget 3 (by decide) 1 0 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc31, hc30, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht034a, ht123e, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht013b, ht123e, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht013b, ht034a, ht123e, hbg3]
                      ·
                        linarith only [hdelta1, ht013b, ht034a, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht123e, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht034a, ht123e, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht023e, hbg3c]
                      ·
                        linarith only [hdelta1, ht013b, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht013b, ht034a, hbg3c]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb3 := m.budget 3 (by decide) 1 4 0 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc31, hc30, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht013d, ht034a, hbg3]
                      ·
                        linarith only [hdelta1, ht023c, ht123e, hbg3, ht134a]
                      ·
                        linarith only [hdelta1, ht034a, ht123e, hbg3, ht134a]
                      ·
                        linarith only [hdelta1, ht023c, ht034a, hbg3, ht134a]
                      ·
                        linarith only [hdelta1, ht023c, ht123e, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123e, hbg3c]
                      ·
                        linarith only [hdelta1, ht023c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht123e, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023c, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht134a, hbg3c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013b, ht023c, ht234a, ht134a]
                    ·
                      have hb0 := m.budget 0 (by decide) 2 4 3 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht012e, ht013a, ht034d, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht012e, ht013c, ht024c, ht234d, ht134a, hbg3, hbg0]
                        ·
                          linarith only [hn, hdelta1, h020, h231, ht034c, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht012e, ht013a, ht023c, ht034c, ht134a, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht012e, ht013c, ht024c, hbg3c, ht234d, hbg0]
                        ·
                          linarith only [hdelta1, h120, h231, ht012b, ht034c, hbg3b, hbg0]
                        ·
                          linarith only [hdelta1, ht012e, ht013a, ht023c, ht034c, hbg3c, hbg0]
                        ·
                          linarith only [hdelta1, h120, h231, ht012b, ht034c, hbg3b, hbg0]
                        ·
                          linarith only [hdelta1, ht023c, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, h120, h231, ht012b, ht034c, hbg3a, hbg0]
                      ·
                        have hb1 := m.budget 1 (by decide) 2 4 3 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hn, hdelta1, h011, h120, ht013c, ht014b, hbg0, hbg1]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc40, hc42] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h340, ht013a, hbg4, hbg1]
                          ·
                            linarith only [hn, hdelta1, h011, h120, ht013c, ht124b, hbg4, hbg0]
                          ·
                            linarith only [hdelta1, ht013a, ht014e, ht134b, hbg4, ht234d, hbg1]
                          ·
                            linarith only [hdelta1, ht012e, ht013a, ht024a, ht134b, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, ht013a, hbg4a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, ht013a, hbg4a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, ht013a, hbg4a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, ht124b, hbg4a, hbg0]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, ht124b, hbg4a, hbg0]
                          ·
                            linarith only [hdelta1, ht012e, ht013a, ht134b, hbg4c, hbg1, ht024b]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc40, hc42] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h340, ht134c, hbg4, hbg1]
                          ·
                            linarith only [hn, hdelta1, h011, h140, ht013c, hbg4, hbg0]
                          ·
                            linarith only [hdelta1, ht012e, ht234d, ht134a, hbg4, hbg1, ht024b]
                          ·
                            linarith only [hdelta1, ht012e, ht024a, ht134a, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, ht134c, hbg4a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, ht134c, hbg4a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, ht134c, hbg4a, hbg1]
                          ·
                            linarith only [hdelta1, h031, h140, hbg0, hbg4a]
                          ·
                            linarith only [hdelta1, h031, h140, hbg0, hbg4a]
                          ·
                            linarith only [hdelta1, ht012e, ht134a, hbg1, hbg4c, ht024b]
                        ·
                          linarith only [hn, hdelta1, ht012b, ht013c, hbg0, hbg1, ht024b]
                        ·
                          linarith only [hdelta1, h011, h120, ht013c, ht014b, hbg1a, hbg0]
                        ·
                          linarith only [hdelta1, h011, h120, ht013c, ht014b, hbg1a, hbg0]
                        ·
                          linarith only [hdelta1, h011, h120, ht013c, ht014b, hbg1a, hbg0]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc40, hc42] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h340, hbg4, hbg1c]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, ht124b, hbg1b, hbg1a, hbg0, hbg4]
                          ·
                            linarith only [hdelta1, ht012e, ht134b, ht234d, ht024b, hbg4, hbg1c]
                          ·
                            linarith only [hdelta1, ht012e, ht024a, ht134b, hbg4, hbg1c]
                          ·
                            linarith only [hdelta1, h011, h340, hbg4a, hbg1c]
                          ·
                            linarith only [hdelta1, h011, h340, hbg4a, hbg1c]
                          ·
                            linarith only [hdelta1, h011, h340, hbg4a, hbg1c]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, ht124b, hbg4a, hbg0]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, ht124b, hbg4a, hbg0]
                          ·
                            linarith only [hdelta1, ht012e, ht134b, hbg4c, ht024b, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht013c, hbg1b, hbg0, ht024b]
                        ·
                          linarith only [hdelta1, ht012b, ht013c, hbg1b, hbg0, ht024b]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc41, hc40, hc42] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hn, hdelta1, h011, h340, ht014b, ht034c, hbg4, hbg0]
                        ·
                          linarith only [hn, hdelta1, h011, h140, ht034c, hbg4, hbg0]
                        ·
                          linarith only [hdelta1, ht013b, ht014e, ht234d, ht134a, hbg4, hbg0]
                        ·
                          linarith only [hdelta1, ht012e, ht013b, ht024a, ht134a, hbg4, hbg0]
                        ·
                          linarith only [hdelta1, h011, h340, ht034c, hbg4a, hbg0, hbg4b]
                        ·
                          linarith only [hdelta1, h011, h340, ht014b, ht034c, hbg4a, hbg0]
                        ·
                          linarith only [hdelta1, h011, h340, ht014b, ht034c, hbg4a, hbg0]
                        ·
                          linarith only [hdelta1, h011, h140, ht034c, hbg4a, hbg0]
                        ·
                          linarith only [hdelta1, h011, h140, ht034c, hbg4a, hbg0]
                        ·
                          linarith only [hdelta1, ht012e, ht013b, hbg4c, ht134a, hbg0, ht024b]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht013a, ht024a, ht234d, hbg0, hbg3]
                        ·
                          linarith only [hdelta1, ht013c, ht024a, ht234d, ht134a, hbg0, hbg3]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc40, hc42] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hn, hdelta1, h231, h340, ht014a, ht023b, hbg4, hbg0, hbg3]
                          ·
                            linarith only [hn, hdelta1, h140, h231, ht034c, hbg4, hbg3]
                          ·
                            linarith only [hdelta1, ht013a, hbg4, ht234d, ht134a, hbg0, ht024b]
                          ·
                            linarith only [hdelta1, ht013a, ht024a, hbg4, ht134a, hbg0]
                          ·
                            linarith only [hdelta1, h231, h340, ht014c, ht023b, hbg4a, hbg0, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, h231, h340, ht014a, ht023b, hbg4a, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, h231, h340, ht014a, ht023b, hbg4a, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, h140, h231, ht034c, hbg4a, hbg3]
                          ·
                            linarith only [hdelta1, h140, h231, ht034c, hbg4a, hbg3]
                          ·
                            linarith only [hdelta1, ht013a, ht134a, hbg4c, hbg0, ht024b]
                        ·
                          linarith only [hdelta1, ht013a, ht023a, ht134a, hbg0, hbg3]
                        ·
                          linarith only [hdelta1, ht013c, ht024a, ht234d, hbg0, hbg3c]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 4 3 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h120, h231, ht014a, ht023b, hbg1, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, h140, h231, ht013b, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, h231, h340, ht034c, hbg1, hbg3a, hbg0, hbg3b, ht024b]
                          ·
                            have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc41, hc40, hc42] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, h231, h340, ht012b, ht014a, ht023b, hbg1, hbg4, hbg3b]
                            ·
                              linarith only [hdelta1, h140, h231, ht034c, hbg4, hbg3b]
                            ·
                              linarith only [hdelta1, h241, h340, ht012b, ht013a, hbg1, hbg3a, hbg4, ht024b]
                            ·
                              linarith only [hdelta1, ht012b, ht013a, ht024a, hbg1, hbg3a, hbg4]
                            ·
                              linarith only [hdelta1, ht014c, ht124b, hbg4b, hbg1]
                            ·
                              linarith only [hdelta1, ht014b, hbg4c, ht234d]
                            ·
                              linarith only [hdelta1, ht012b, ht014a, ht024a, hbg1, hbg4c]
                            ·
                              linarith only [hdelta1, ht013c, ht034c, ht124b, hbg4a, hbg1]
                            ·
                              linarith only [hdelta1, ht013c, ht034c, ht124b, hbg4a, hbg1]
                            ·
                              linarith only [hdelta1, ht013a, hbg3a, hbg4c, hbg0, ht024b]
                          ·
                            linarith only [hdelta1, h011, h120, ht013a, hbg1c]
                          ·
                            linarith only [hdelta1, h231, h340, ht034c, hbg0, hbg3c, ht024b, hbg1b]
                          ·
                            linarith only [hdelta1, ht014a, hbg1c]
                          ·
                            linarith only [hdelta1, h231, h340, ht034c, hbg1b, hbg0, hbg3c, ht024b]
                          ·
                            linarith only [hdelta1, ht013a, ht124b, hbg1c]
                          ·
                            linarith only [hdelta1, h231, h340, ht034c, hbg1a, hbg0, hbg3c, ht024b]
                        ·
                          linarith only [hdelta1, ht013a, ht024a, ht234c, hbg0, hbg3c]
                        ·
                          linarith only [hdelta1, ht123e, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht023a, ht134a, hbg0, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht034c, ht134a, hbg0, hbg3c, ht024b]
                      ·
                        linarith only [hdelta1, ht012e, ht013c, hbg0c]
                      ·
                        linarith only [hdelta1, ht012e, ht034c, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht013a, ht034d, hbg0c, hbg3]
                        ·
                          linarith only [hdelta1, ht013c, ht034d, ht134a, hbg0c, hbg3]
                        ·
                          linarith only [hdelta1, h020, h231, ht034c, hbg0a, hbg3]
                        ·
                          linarith only [hdelta1, ht013a, ht023c, ht034c, ht134a, hbg0c, hbg3]
                        ·
                          linarith only [hdelta1, ht013c, ht024c, hbg3c, ht234d, hbg0c]
                        ·
                          linarith only [hdelta1, h231, h340, ht013a, ht034c, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, ht013a, ht023c, ht034c, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, ht123e, hbg3c]
                        ·
                          linarith only [hdelta1, ht023c, hbg3c, ht134a]
                        ·
                          linarith only [hdelta1, ht013b, hbg3c, ht134a]
                      ·
                        linarith only [hdelta1, ht014e, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc40, hc42] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h011, h340, ht013c, ht014b, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, h011, h140, ht013c, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, ht013a, hbg3, ht234d, hbg4, hbg0b, ht024b]
                          ·
                            linarith only [hdelta1, ht013a, ht024a, hbg3, hbg4, hbg0b]
                          ·
                            linarith only [hdelta1, h011, h340, ht013c, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, ht014b, hbg4c, ht234d]
                          ·
                            linarith only [hdelta1, ht013c, ht024a, ht014b, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht124e, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, ht024a, hbg0c, hbg4c, ht134b]
                          ·
                            linarith only [hdelta1, ht013a, hbg3, hbg4c, hbg0b, ht024b]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc40, hc42] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h340, ht013c, ht134c, hbg3, hbg4]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, ht124b, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, ht013c, hbg3, hbg4, ht234d, ht134a, hbg0b, ht024b]
                          ·
                            linarith only [hdelta1, ht013c, ht024a, hbg3, hbg4, ht134a, hbg0b]
                          ·
                            linarith only [hdelta1, h011, h340, ht013c, ht134c, hbg3, hbg4a]
                          ·
                            linarith only [hdelta1, h011, h340, ht013c, ht134c, hbg3, hbg4a]
                          ·
                            linarith only [hdelta1, h011, h340, ht013c, ht134c, hbg3, hbg4a]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, ht124b, hbg3, ht234d, ht134a, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, ht024a, hbg0c, ht134b, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, hbg3, ht134a, hbg0b, hbg4c, ht024b]
                        ·
                          linarith only [hdelta1, h040, h231, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, ht023c, ht034b, hbg3, hbg0a]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc40, hc42] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h011, h340, ht013c, ht014b, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, h011, h140, ht013c, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, ht013c, hbg4, ht234d, hbg0b, ht024b, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht024a, hbg4, hbg0b, hbg3c]
                          ·
                            linarith only [hdelta1, h011, h340, ht013c, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, ht014b, hbg4c, ht234d]
                          ·
                            linarith only [hdelta1, ht013c, ht024a, ht014b, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht124e, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, ht024a, hbg0c, hbg4c, ht134b]
                          ·
                            linarith only [hdelta1, ht013c, hbg4c, hbg0b, ht024b, hbg3c]
                        ·
                          linarith only [hdelta1, h231, h340, ht013a, hbg0c, ht024b, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht023c, hbg0c, ht024b, hbg3c]
                        ·
                          linarith only [hdelta1, ht123e, hbg3c]
                        ·
                          linarith only [hdelta1, ht023c, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht134a, hbg3c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc41, hc40, hc42] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h011, h340, ht014b, ht034c, hbg0a, hbg4]
                        ·
                          linarith only [hdelta1, h011, h140, ht034c, hbg0a, hbg4]
                        ·
                          linarith only [hdelta1, ht034a, hbg0c, ht234d, hbg4, ht024b]
                        ·
                          linarith only [hdelta1, ht013b, ht024a, hbg0c, ht134a, hbg4]
                        ·
                          linarith only [hdelta1, h011, h340, ht034c, hbg0a, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, hbg4c, ht234d]
                        ·
                          linarith only [hdelta1, ht024a, ht014b, ht034c, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht124e, hbg4c]
                        ·
                          linarith only [hdelta1, ht024a, ht034c, hbg0c, ht134b, hbg4c]
                        ·
                          linarith only [hdelta1, ht013b, hbg0c, hbg4c, ht134a, ht024b]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht023b, ht024c, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb3 := m.budget 3 (by decide) 1 4 0 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc31, hc30, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht034a, ht013d, hbg3]
                      ·
                        linarith only [hdelta1, ht023c, hbg3, ht134a, ht123e]
                      ·
                        linarith only [hdelta1, ht034a, hbg3, ht134a, ht123e]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg3, ht234b, ht134a]
                      ·
                        linarith only [hdelta1, ht013d, hbg3c]
                      ·
                        linarith only [hdelta1, ht023b, ht024a, ht234b, ht123e, hbg3c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht234b, hbg3c]
                      ·
                        linarith only [hdelta1, ht134a, ht123e, hbg3c]
                      ·
                        linarith only [hdelta1, ht023c, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht134a, hbg3c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013b, ht023c, ht134a, ht234a]
                    ·
                      have hb0 := m.budget 0 (by decide) 4 2 3 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        linarith only [hdelta1, h120, h231, ht024b, ht023a, ht124a, hbg0]
                      ·
                        linarith only [hdelta1, h011, h120, ht013c, ht024a, ht124a, hbg0]
                      ·
                        linarith only [hdelta1, h011, h120, ht023b, ht024a, ht124a, hbg0]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc42, hc40] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht023a, ht024a, ht124c, hbg4]
                          ·
                            linarith only [hdelta1, h140, h231, ht023a, ht024a, hbg4]
                          ·
                            linarith only [hdelta1, h120, h231, ht023a, ht024c, ht124a, hbg4]
                          ·
                            linarith only [hn, hdelta1, ht013a, hbg0, hbg4, hbg3]
                          ·
                            linarith only [hdelta1, h231, h340, ht023a, ht024a, hbg4c]
                          ·
                            linarith only [hdelta1, h231, h340, ht023a, ht024c, hbg4c, ht124c]
                          ·
                            linarith only [hdelta1, ht013a, hbg4b, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht014d, hbg4c]
                          ·
                            linarith only [hdelta1, ht013a, hbg0, hbg4b, hbg3]
                          ·
                            linarith only [hdelta1, ht013a, hbg0, hbg4b, hbg3]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc42, hc40] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht023a, ht024a, ht124c, hbg4]
                          ·
                            linarith only [hdelta1, h140, h231, ht023a, ht024a, hbg4]
                          ·
                            linarith only [hdelta1, h120, h231, ht023a, ht024c, ht124a, hbg4]
                          ·
                            linarith only [hn, hdelta1, ht013c, ht134a, hbg0, hbg4, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, ht013c, hbg4a, ht134c, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, ht013c, hbg4a, ht134c, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, ht013c, hbg4a, ht134c, hbg3]
                          ·
                            linarith only [hdelta1, h120, h231, ht023a, ht024c, ht124b, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, ht134a, hbg0, hbg4b, hbg3]
                          ·
                            linarith only [hdelta1, ht013c, ht134a, hbg0, hbg4b, hbg3]
                        ·
                          linarith only [hdelta1, h120, h231, ht023b, ht024a, ht124a, hbg3]
                        ·
                          linarith only [hdelta1, ht013a, ht023a, ht024c, ht134a, hbg0, hbg3]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc42, hc40] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht023a, ht024a, ht124c, hbg4]
                          ·
                            linarith only [hdelta1, h140, h231, ht023a, ht024a, hbg4]
                          ·
                            linarith only [hdelta1, h120, h231, ht023a, ht024c, ht124a, hbg4]
                          ·
                            linarith only [hdelta1, ht013c, hbg3a, hbg3b, hbg0, hbg4]
                          ·
                            linarith only [hdelta1, h231, h340, ht023a, ht024a, hbg4c]
                          ·
                            linarith only [hdelta1, h231, h340, ht023a, ht024c, hbg4c, ht124c]
                          ·
                            linarith only [hdelta1, ht013c, hbg4b, hbg0, hbg3c]
                          ·
                            linarith only [hdelta1, ht014d, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, hbg4b, hbg0, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, hbg4b, hbg0, hbg3c]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 4 3 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h120, h231, ht014b, ht023b, ht024c, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, h140, h231, ht013b, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, h011, h340, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht012c, ht024a, hbg1, ht124a]
                          ·
                            linarith only [hdelta1, h120, h231, ht013b, hbg1c, hbg3b]
                          ·
                            linarith only [hdelta1, h231, h340, ht023b, ht024c, hbg1b, hbg0, hbg3c]
                          ·
                            linarith only [hdelta1, ht014a, hbg1c]
                          ·
                            linarith only [hdelta1, h231, h340, ht023b, ht024c, hbg1b, hbg0, hbg3c]
                          ·
                            linarith only [hdelta1, ht013a, hbg1c, ht124b]
                          ·
                            linarith only [hdelta1, h231, h340, ht023b, ht024c, hbg1a, hbg0, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht023a, ht024c, hbg0, hbg3c]
                        ·
                          linarith only [hdelta1, ht123e, hbg3c]
                        ·
                          linarith only [hdelta1, ht023c, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, h011, h120, ht013c, ht024b, ht124a, hbg0c]
                      ·
                        linarith only [hdelta1, h011, h120, ht024b, ht023b, ht124a, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h231, h340, ht013a, ht023a, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, ht013c, ht023a, hbg3, hbg0c, ht123e]
                        ·
                          linarith only [hdelta1, h040, h231, ht023b, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, ht023a, ht034b, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h231, h340, ht013c, ht023a, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, h231, h340, ht013a, ht023b, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht023a, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht123e, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht023a, ht134a, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht023b, ht134a, hbg0c, hbg3c]
                      ·
                        linarith only [hdelta1, h011, h140, ht024a, ht124c, hbg0c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 1 2 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc41, hc42, hc40] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h011, h340, ht013c, ht014b, ht024c, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h011, h140, ht013c, ht024a, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h011, h240, ht013c, ht024c, hbg4, hbg0a]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht013a, hbg4, hbg0b, hbg3]
                          ·
                            linarith only [hdelta1, ht013c, hbg4, ht134a, hbg0b, hbg3]
                          ·
                            linarith only [hdelta1, h120, h231, ht024a, ht124a, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht014b, ht023c, ht024c, ht134b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht013c, hbg4, hbg0b, hbg3c]
                          ·
                            linarith only [hdelta1, h120, h231, ht013a, ht024a, hbg4, ht124a, hbg3c, hbg0c]
                          ·
                            linarith only [hdelta1, ht013a, ht023c, ht024c, hbg3c, hbg0c]
                          ·
                            linarith only [hdelta1, hbg3c, ht123e]
                          ·
                            linarith only [hdelta1, ht023c, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, ht024a, ht124c, ht134b, hbg3c, hbg0a]
                        ·
                          linarith only [hdelta1, h021, h340, ht024a, hbg4c]
                        ·
                          linarith only [hdelta1, h011, h340, ht013c, ht024c, hbg4c, ht124c, hbg0a]
                        ·
                          linarith only [hdelta1, ht013c, ht024a, hbg4c, ht124c, hbg0c]
                        ·
                          linarith only [hdelta1, h011, h120, ht013c, ht024c, hbg4c, ht124b, hbg0a]
                        ·
                          linarith only [hdelta1, ht013c, ht024a, hbg4c, ht134b, hbg0c]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 4 3 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h021, h120, ht024c, ht124c, hbg4a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h120, ht013a, hbg4c, ht124a, ht134b, hbg1]
                          ·
                            linarith only [hdelta1, h011, h120, hbg4c, ht124a, ht134a, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht024c, hbg4a, ht124a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h120, ht013a, hbg1c]
                          ·
                            linarith only [hdelta1, h011, h120, hbg4c, ht124c, ht134a, hbg1c]
                          ·
                            linarith only [hdelta1, ht013c, ht024c, ht124c, hbg4a, hbg1c, hbg0a]
                          ·
                            linarith only [hdelta1, h011, h120, hbg4c, ht124a, ht134b, hbg1c]
                          ·
                            linarith only [hdelta1, ht013a, hbg4c, ht124a, ht134b, hbg1c]
                          ·
                            linarith only [hdelta1, hbg4c, ht124a, ht134a, hbg1c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h340, ht013b, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h011, h130, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h120, h231, ht023b, ht024a, hbg3, ht124a]
                        ·
                          linarith only [hdelta1, ht023a, ht024a, ht124c, hbg3, ht134b]
                        ·
                          linarith only [hdelta1, h011, h340, hbg0a, hbg3c]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc42, hc40] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h011, h340, ht014b, ht023b, ht024c, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, h011, h140, ht023b, ht024a, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, h011, h240, ht023b, ht024c, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, ht013b, hbg3a, hbg0c, hbg4]
                          ·
                            linarith only [hdelta1, h011, h340, ht023b, ht024a, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, h011, h340, ht023b, ht024c, ht124c, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, ht023b, ht024a, ht124c, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, h011, h120, ht023b, ht024c, ht124b, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, ht023b, ht024a, hbg0c, hbg4c, ht134b]
                          ·
                            linarith only [hdelta1, h120, h231, ht013b, hbg4c, ht124a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht023a, ht024c, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, h231, h340, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht023a, ht024c, hbg0c, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht134a, hbg3c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht123b, ht124c, ht134b]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013b, ht023c, ht234a, ht134a]
                    ·
                      have hb1 := m.budget 1 (by decide) 4 2 3 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012b, ht023a, ht234e, ht124b, hbg1]
                      ·
                        linarith only [hdelta1, ht013b, ht023c, ht124a, ht234e, hbg1]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hn, hdelta1, h011, h340, hbg3, hbg1]
                        ·
                          linarith only [hdelta1, ht023c, hbg3, ht123b, ht124a, ht234e]
                        ·
                          linarith only [hdelta1, ht013b, hbg3, ht123b, ht124a, ht234e]
                        ·
                          linarith only [hdelta1, ht012e, ht023a, hbg3, ht134a, hbg1]
                        ·
                          linarith only [hdelta1, h011, h340, hbg3a, hbg1]
                        ·
                          linarith only [hdelta1, h011, h340, hbg3a, hbg1]
                        ·
                          linarith only [hdelta1, h011, h340, hbg3a, hbg1]
                        ·
                          linarith only [hdelta1, ht123b, hbg3c, ht124a, ht234e]
                        ·
                          linarith only [hdelta1, ht023c, ht123b, hbg3c, ht124a, ht234b]
                        ·
                          linarith only [hdelta1, ht013b, ht123b, hbg3c, ht124a, ht234b]
                      ·
                        have hb0 := m.budget 0 (by decide) 4 2 3 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hn, hdelta1, ht013c, ht014b, ht023b, hbg0, hbg1]
                        ·
                          linarith only [hdelta1, ht012b, ht023c, ht124a, hbg0, ht234e]
                        ·
                          linarith only [hn, hdelta1, ht013b, ht123b, ht124c, hbg0, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            have hb4 := m.budget 4 (by decide) 3 2 1 0 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc42, hc41, hc40] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, h011, h340, ht013a, ht123b, ht124a, hbg4]
                            ·
                              linarith only [hdelta1, ht014b, ht023a, ht024c, ht234e, hbg4]
                            ·
                              linarith only [hdelta1, ht023a, ht024c, ht234e, hbg4, ht124b]
                            ·
                              linarith only [hn, hdelta1, ht013a, ht014b, hbg3, hbg4, hbg1]
                            ·
                              linarith only [hdelta1, h231, h340, ht014b, ht023a, ht024c, hbg4c]
                            ·
                              linarith only [hdelta1, ht013c, ht023b, ht024c, hbg4b, hbg1]
                            ·
                              linarith only [hdelta1, ht013a, ht014b, hbg3, hbg4b, hbg1]
                            ·
                              linarith only [hdelta1, h041, h340, ht013a, hbg3, hbg4b, hbg1]
                            ·
                              linarith only [hdelta1, ht013a, ht014b, hbg3, hbg4b, hbg1]
                            ·
                              linarith only [hdelta1, ht013a, hbg3, hbg4a, hbg4b, hbg1]
                          ·
                            linarith only [hn, hdelta1, ht013c, hbg3, ht123b, ht124c, hbg1]
                          ·
                            linarith only [hdelta1, ht013b, hbg3, ht123b, ht124a, ht234e]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, hbg3, ht124a, ht234b]
                          ·
                            linarith only [hdelta1, ht013c, ht123b, ht124c, hbg3b, hbg1]
                          ·
                            have hb4 := m.budget 4 (by decide) 3 2 1 0 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc42, hc41, hc40] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, h231, h340, ht023b, ht024a, hbg3b, hbg4]
                            ·
                              linarith only [hdelta1, h231, h240, ht014b, ht023b, ht024c, hbg3b, hbg4]
                            ·
                              linarith only [hdelta1, h140, h231, ht023b, ht024c, hbg3b, hbg4]
                            ·
                              linarith only [hdelta1, ht013a, ht014b, hbg3a, hbg1, hbg4]
                            ·
                              linarith only [hdelta1, h231, h340, ht014b, ht023b, ht024c, hbg3b, hbg4c]
                            ·
                              linarith only [hdelta1, ht013c, ht023b, ht024c, hbg4b, hbg1]
                            ·
                              linarith only [hdelta1, ht012a, ht014b, ht124a, hbg4c, hbg1]
                            ·
                              linarith only [hdelta1, ht014c, hbg1, hbg4b]
                            ·
                              linarith only [hdelta1, ht013b, ht014b, ht234e, hbg3c, hbg4c]
                            ·
                              linarith only [hdelta1, ht012c, ht024c, hbg1, hbg4a]
                          ·
                            linarith only [hdelta1, ht013a, ht014b, ht023a, ht024c, hbg3c, hbg1]
                          ·
                            linarith only [hdelta1, ht013c, ht123b, ht124c, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, ht013c, ht123b, ht124c, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, ht012b, ht013c, hbg0b, ht124c, hbg1]
                        ·
                          linarith only [hdelta1, ht013b, hbg0b, ht123b, ht124c, hbg1]
                        ·
                          linarith only [hdelta1, ht012c, ht014b, hbg0a, hbg1]
                        ·
                          linarith only [hdelta1, ht014b, ht024c, hbg0a, hbg0b, hbg1]
                        ·
                          linarith only [hdelta1, ht013c, ht014b, ht024c, hbg0a, hbg1]
                        ·
                          linarith only [hdelta1, ht014b, ht023b, ht024c, hbg0a, hbg1]
                      ·
                        linarith only [hdelta1, h011, h340, ht013a, hbg1c, ht234b, ht124b]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h340, hbg3, hbg1b]
                        ·
                          linarith only [hdelta1, h031, h140, ht123b, hbg1a, hbg3]
                        ·
                          linarith only [hdelta1, ht013b, ht123b, hbg1a, hbg3, ht234e, ht124b]
                        ·
                          linarith only [hdelta1, ht012b, ht023a, hbg1a, hbg3, ht234b, ht124b]
                        ·
                          linarith only [hdelta1, h011, h340, ht023c, ht123b, hbg1c, ht234e, ht124b, hbg3c]
                        ·
                          linarith only [hdelta1, h011, h340, ht013b, ht123b, hbg1c, ht234e, ht124b, hbg3c]
                        ·
                          linarith only [hdelta1, h011, h140, ht012b, ht023a, hbg1c, hbg3c]
                        ·
                          linarith only [hdelta1, ht123b, hbg1a, ht234e, ht124b, hbg3c]
                        ·
                          linarith only [hdelta1, ht023c, ht123b, hbg1a, ht234b, ht124b, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht123b, hbg1a, ht234b, ht124b, hbg3c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, h011, h340, ht124a, ht234b, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124c, hbg1c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h340, hbg1a, hbg3]
                        ·
                          linarith only [hdelta1, ht023c, ht123b, ht124a, ht234e, hbg3]
                        ·
                          linarith only [hdelta1, ht023b, ht024a, ht234e, hbg3]
                        ·
                          linarith only [hdelta1, ht023a, ht024a, ht234b, hbg3]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc42, hc41, hc40] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h011, h340, ht012a, hbg4, ht124a]
                          ·
                            linarith only [hdelta1, h031, h240, ht123b, ht124c, hbg4, hbg3b]
                          ·
                            linarith only [hdelta1, ht023a, ht024c, hbg4, ht234e, ht124b]
                          ·
                            linarith only [hdelta1, ht013c, ht014b, hbg4, hbg3c, hbg1b]
                          ·
                            linarith only [hdelta1, h011, h340, ht013c, ht123b, ht124c, hbg3b, hbg4c]
                          ·
                            linarith only [hdelta1, h231, h340, ht023a, ht024c, hbg4c, ht124b]
                          ·
                            linarith only [hdelta1, ht014b, ht123b, ht124a, hbg4c, hbg1c]
                          ·
                            linarith only [hdelta1, h231, h240, ht023a, ht024c, hbg4c]
                          ·
                            linarith only [hdelta1, ht014b, ht023c, hbg3c, ht234e, hbg4c]
                          ·
                            linarith only [hdelta1, ht023c, ht123b, ht124a, hbg3c, ht234e, hbg4c, hbg1c]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc42, hc41, hc40] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht023b, ht024a, hbg4, hbg3b]
                          ·
                            linarith only [hdelta1, h231, h240, ht014b, ht023b, ht024c, hbg4, hbg3b]
                          ·
                            linarith only [hdelta1, h140, h231, ht023b, ht024c, hbg4, hbg3b]
                          ·
                            linarith only [hdelta1, ht014b, hbg3a, hbg4, hbg1c]
                          ·
                            linarith only [hdelta1, h231, h340, ht014b, ht023b, ht024c, hbg4c, hbg3b]
                          ·
                            linarith only [hdelta1, h231, h340, ht023b, ht024c, hbg3c, hbg1c, hbg4b]
                          ·
                            linarith only [hdelta1, ht014b, ht123b, ht124a, hbg4c, hbg1c]
                          ·
                            linarith only [hdelta1, h231, h340, ht023b, ht024c, hbg3c, hbg1c, hbg4b]
                          ·
                            linarith only [hdelta1, ht013b, ht014b, hbg3c, ht234e, hbg4c]
                          ·
                            linarith only [hdelta1, h231, h340, ht023b, ht024c, hbg3c, hbg1c, hbg4a]
                        ·
                          linarith only [hdelta1, ht012b, ht023a, ht124c, hbg3c, hbg1c]
                        ·
                          linarith only [hdelta1, hbg3c, ht123e]
                        ·
                          linarith only [hdelta1, ht023c, ht123b, ht124a, hbg3c, ht234b]
                        ·
                          linarith only [hdelta1, ht013b, ht123b, ht124a, hbg3c, ht234b]
              ·
                linarith only [ht012b, ht023a, ht123a]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 1 2 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc31, hc32, hc30] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, h120, h241, ht024a, ht023a, hbg3, ht123b]
                      ·
                        linarith only [hdelta1, h120, h341, ht024a, ht123a, ht023c, ht234c, hbg3]
                      ·
                        have hb0 := m.budget 0 (by decide) 3 2 4 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, h120, h241, ht024a, ht023b, ht123a, hbg0]
                        ·
                          linarith only [hdelta1, h120, h341, ht023a, ht024c, ht123a, ht234c, hbg0]
                        ·
                          linarith only [hdelta1, h011, h120, ht023a, ht024b, ht123a, hbg0]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hn, hdelta1, h120, h341, ht013a, hbg3, hbg1, hbg0]
                          ·
                            linarith only [hn, hdelta1, h130, h341, ht014a, hbg3, hbg1, hbg0]
                          ·
                            linarith only [hn, hdelta1, hbg3, ht134e, hbg1, hbg0]
                          ·
                            linarith only [hdelta1, ht012c, ht023a, ht123a, hbg1]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, hbg3, hbg1b, ht123b, hbg0, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht014a, hbg3, ht123b, hbg0, hbg1a]
                          ·
                            linarith only [hdelta1, hbg3, ht134e, hbg0, hbg1a]
                        ·
                          linarith only [hdelta1, h120, h341, ht023b, ht024c, ht123a, hbg0c, ht234c]
                        ·
                          linarith only [hdelta1, h011, h120, ht023b, ht024b, ht123a, hbg0c]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h120, h241, ht013a, ht024a, hbg0c, hbg1]
                          ·
                            linarith only [hdelta1, h120, h341, ht014a, hbg1, hbg3, ht123b, hbg0b]
                          ·
                            linarith only [hdelta1, ht024a, ht124e, hbg0c, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht013b, hbg1, hbg0a, ht123b]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht024a, hbg0c, ht234c, ht123b, hbg1c]
                          ·
                            linarith only [hdelta1, ht014a, ht123b, hbg1c]
                          ·
                            linarith only [hdelta1, ht023b, ht123a, hbg3, ht134e, hbg1c]
                        ·
                          linarith only [hdelta1, ht012e, hbg0c]
                        ·
                          linarith only [hdelta1, h120, h341, ht014c, ht023a, ht123a, hbg0c, hbg3]
                        ·
                          linarith only [hdelta1, h120, h341, ht023a, ht024b, ht123a, hbg0c, hbg3]
                      ·
                        linarith only [hdelta1, ht024a, ht023a, ht234c, hbg3, ht123c]
                      ·
                        linarith only [hdelta1, h120, h341, ht024a, ht023c, ht234c, hbg3c, ht123b]
                      ·
                        have hb0 := m.budget 0 (by decide) 3 2 4 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, h021, h120, ht023b, hbg0, hbg3a, ht123b]
                        ·
                          linarith only [hdelta1, h041, h120, ht023a, hbg0, hbg3a, ht123b]
                        ·
                          linarith only [hdelta1, h011, h120, ht023a, ht024b, hbg0, hbg3a, ht123b]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h021, h120, ht023a, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h120, h341, ht014a, hbg0, ht123b, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, hbg0, ht134e, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht023a, hbg3a, ht123b, hbg1]
                          ·
                            linarith only [hdelta1, h120, h341, ht023b, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht023b, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht023b, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, h130, h341, hbg0, hbg3b, hbg1c]
                          ·
                            linarith only [hdelta1, ht014a, ht123b, hbg1c]
                          ·
                            linarith only [hdelta1, ht023b, hbg3c, ht134e, ht123b, hbg1c]
                        ·
                          linarith only [hdelta1, h120, h341, ht023b, ht024c, hbg0c, hbg3a, ht234c, ht123b]
                        ·
                          linarith only [hdelta1, h011, h120, ht023b, ht024b, hbg0c, hbg3a, ht123b]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h021, h120, ht023b, hbg3a, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, h120, h341, ht014a, ht024a, hbg0c, ht234c, ht123b, hbg1]
                          ·
                            linarith only [hdelta1, ht024a, ht124e, hbg0c, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht023b, hbg3a, ht123b, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, h120, h341, ht023b, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht023b, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, h120, h341, ht023b, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, h130, h341, ht024a, hbg0c, ht234c, hbg1c]
                          ·
                            linarith only [hdelta1, ht014a, ht123b, hbg1c]
                          ·
                            linarith only [hdelta1, ht023b, hbg3c, ht134e, ht123b, hbg1c]
                        ·
                          linarith only [hdelta1, h011, h120, ht023a, hbg3a, ht123b, hbg0c]
                        ·
                          linarith only [hdelta1, h120, h341, ht014c, ht023a, hbg3c, ht123b, hbg0c]
                        ·
                          linarith only [hdelta1, h120, h341, ht023a, ht024b, hbg3c, ht123b, hbg0c]
                      ·
                        linarith only [hdelta1, ht024a, ht023a, ht234c, hbg3c]
                      ·
                        linarith only [hdelta1, h120, h341, ht123a, hbg3c]
                      ·
                        linarith only [hdelta1, ht024a, ht023c, ht234c, hbg3c, ht123c]
                      ·
                        have hb0 := m.budget 0 (by decide) 3 2 4 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, h120, h241, ht024a, ht023b, ht123a, hbg0]
                        ·
                          linarith only [hdelta1, ht023a, ht024c, ht234c, hbg3b, ht123c, hbg0]
                        ·
                          linarith only [hdelta1, h011, h120, ht023a, ht024b, ht123a, hbg0]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h120, h241, ht024a, ht023a, hbg1, ht123c]
                          ·
                            linarith only [hdelta1, h130, h341, ht014a, hbg1, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, hbg1, ht134b, hbg3b, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, ht012c, ht023a, ht123a, hbg1]
                          ·
                            linarith only [hdelta1, ht014a, hbg3c, hbg0, hbg1b]
                          ·
                            linarith only [hdelta1, hbg3c, ht134b, hbg0, hbg1b]
                          ·
                            linarith only [hdelta1, ht014c, ht023a, ht024b, hbg1c, ht123c]
                          ·
                            linarith only [hdelta1, hbg1b, hbg3c, hbg0, hbg1a]
                          ·
                            linarith only [hdelta1, ht014a, hbg3c, hbg0, hbg1a]
                          ·
                            linarith only [hdelta1, hbg3c, ht134b, hbg0, hbg1a]
                        ·
                          linarith only [hdelta1, ht013e, ht014c, hbg0c]
                        ·
                          linarith only [hdelta1, h011, h120, ht023b, ht024b, ht123a, hbg0c]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h021, h120, ht023b, hbg0a, ht123c, hbg1]
                          ·
                            linarith only [hdelta1, ht014b, ht024c, ht234c, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht024a, ht124e, hbg0c, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht023b, ht123a, hbg0a, hbg1]
                          ·
                            linarith only [hdelta1, h120, h341, ht014a, ht024a, ht234c, hbg0c, hbg1c]
                          ·
                            linarith only [hdelta1, h120, h341, ht024a, ht234c, hbg0c, ht134b, hbg1c]
                          ·
                            linarith only [hdelta1, ht014c, ht023b, ht024b, hbg0a, ht123c, hbg1c]
                          ·
                            linarith only [hdelta1, ht024a, ht234c, hbg0c, hbg3b, hbg1c]
                          ·
                            linarith only [hdelta1, ht014a, ht123b, hbg1c]
                          ·
                            linarith only [hdelta1, ht023b, ht123a, hbg3c, ht134b, hbg1c]
                        ·
                          linarith only [hdelta1, ht012e, hbg0c]
                        ·
                          linarith only [hdelta1, ht014c, ht023a, hbg3c, hbg0c, ht123c]
                        ·
                          linarith only [hdelta1, ht023a, ht024b, hbg3c, hbg0c, ht123c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht013b, ht034c, ht024b, ht023c, ht134a]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 2 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012b, ht024a, ht123b, ht234d, hbg1]
                      ·
                        linarith only [hdelta1, h011, h230, ht014a, ht123a, hbg1]
                      ·
                        have hb0 := m.budget 0 (by decide) 3 2 4 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, h230, h241, ht013e, ht024a, ht124b, ht123a, hbg1, hbg0]
                        ·
                          linarith only [hdelta1, ht012b, ht024c, ht123a, ht234d, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h230, ht013b, ht024b, ht023c, hbg3, hbg0]
                          ·
                            linarith only [hn, hdelta1, h011, h130, ht024b, ht023c, hbg3, hbg0]
                          ·
                            have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc41, hc40, hc42, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hn, hdelta1, h011, h140, hbg0, hbg4]
                            ·
                              linarith only [hdelta1, ht012b, ht024b, ht123a, ht234d, hbg4]
                            ·
                              linarith only [hdelta1, h230, h341, ht012b, ht024a, ht123a, hbg4]
                            ·
                              linarith only [hn, hdelta1, ht013e, ht014b, hbg3, hbg0, hbg4]
                            ·
                              linarith only [hdelta1, h011, h140, hbg4a, hbg0]
                            ·
                              linarith only [hdelta1, h011, h140, hbg4a, hbg0]
                            ·
                              linarith only [hdelta1, h011, h140, hbg4a, hbg0]
                            ·
                              linarith only [hdelta1, h230, h341, ht012b, ht024b, ht123a, hbg4c]
                            ·
                              linarith only [hdelta1, ht013e, ht014b, hbg3, hbg0, hbg4b]
                            ·
                              linarith only [hdelta1, ht013e, ht014b, hbg3, hbg0, hbg4b]
                          ·
                            linarith only [hdelta1, ht012b, ht013e, ht034a, ht024b, ht123a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, h011, h230, ht024b, ht023c, hbg3b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h230, ht013b, ht024b, ht023c, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h230, ht013b, ht024b, ht023c, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h130, ht024b, ht023c, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h130, ht024b, ht023c, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht012b, ht013e, ht024b, ht123a, hbg3c, hbg0]
                        ·
                          linarith only [hdelta1, ht024a, ht124b, ht123a, ht023c, ht234d, hbg1, hbg0]
                        ·
                          linarith only [hdelta1, ht013e, ht024c, ht124b, ht123a, ht234d, hbg0c, hbg1]
                        ·
                          linarith only [hdelta1, ht013e, ht024b, hbg0c]
                        ·
                          linarith only [hdelta1, h230, h241, ht024a, ht124b, ht123a, hbg0c, hbg1]
                        ·
                          linarith only [hdelta1, h011, h230, ht012b, ht123a, hbg0c]
                        ·
                          linarith only [hdelta1, ht024c, ht124b, ht123a, ht023c, ht234d, hbg0c, hbg1]
                        ·
                          have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc41, hc40, hc42, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h011, h120, ht124b, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, ht014b, ht124b, ht123a, ht234d, hbg4]
                          ·
                            linarith only [hdelta1, h230, h341, ht024a, ht124b, ht123a, ht023c, hbg0b, hbg1, hbg4]
                          ·
                            linarith only [hdelta1, ht034a, hbg0b, hbg1, hbg4]
                          ·
                            linarith only [hdelta1, ht124b, ht123a, ht234d, hbg4c]
                          ·
                            linarith only [hdelta1, h230, h341, ht024c, ht124b, ht123a, hbg4c]
                          ·
                            linarith only [hdelta1, ht034a, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, h230, h341, ht014b, ht124b, ht123a, hbg4c]
                          ·
                            linarith only [hdelta1, ht024b, ht023c, ht234c, hbg0b, hbg1, hbg4c]
                          ·
                            linarith only [hdelta1, ht024a, ht023c, hbg0b, hbg1, hbg4c]
                      ·
                        have hb0 := m.budget 0 (by decide) 3 2 4 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, h230, h241, ht012a, ht013b, ht024a, ht123a, hbg0, hbg1]
                        ·
                          linarith only [hn, hdelta1, ht013b, ht014c, ht023c, hbg0, hbg1]
                        ·
                          linarith only [hn, hdelta1, ht014b, ht124b, ht123c, hbg0, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht013b, ht024a, ht023c, ht234d, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht012c, ht023c, hbg3, hbg1]
                          ·
                            have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc41, hc40, hc42, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hn, hdelta1, h230, h341, ht013b, ht014c, ht124b, ht123a, hbg3, hbg4, hbg1]
                            ·
                              linarith only [hdelta1, ht023a, ht024b, ht234d, hbg4]
                            ·
                              linarith only [hdelta1, h230, h341, ht012b, ht024a, ht123a, hbg4]
                            ·
                              linarith only [hn, hdelta1, ht013b, ht014a, hbg3, hbg4, hbg1]
                            ·
                              linarith only [hdelta1, ht014c, ht124b, ht123c, hbg1, hbg4a]
                            ·
                              linarith only [hdelta1, ht014c, ht124b, ht123c, hbg1, hbg4a]
                            ·
                              linarith only [hdelta1, ht014c, ht124b, ht123c, hbg1, hbg4a]
                            ·
                              linarith only [hdelta1, h230, h341, ht014b, ht124b, ht123a, hbg4c]
                            ·
                              linarith only [hdelta1, ht013b, ht014a, hbg3, hbg1, hbg4b]
                            ·
                              linarith only [hdelta1, ht013b, ht014a, hbg3, hbg1, hbg4b]
                          ·
                            linarith only [hdelta1, ht012b, ht024a, ht123a, hbg3, ht234c]
                          ·
                            linarith only [hdelta1, ht014c, ht024b, ht023c, hbg3b, hbg1]
                          ·
                            have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc41, hc40, hc42, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hn, hdelta1, ht014c, ht124b, ht123c, hbg1, hbg4]
                            ·
                              linarith only [hdelta1, ht014b, ht124b, ht123c, ht234d, hbg3a, hbg4]
                            ·
                              linarith only [hdelta1, h230, h341, ht012b, ht024a, ht123c, hbg3a, hbg4]
                            ·
                              linarith only [hdelta1, ht013b, ht014a, hbg3b, hbg1, hbg4]
                            ·
                              linarith only [hdelta1, ht014c, ht124b, ht123c, hbg1, hbg4a]
                            ·
                              linarith only [hdelta1, ht014c, ht124b, ht123c, hbg1, hbg4a]
                            ·
                              linarith only [hdelta1, ht014c, ht124b, ht123c, hbg1, hbg4a]
                            ·
                              linarith only [hdelta1, h230, h341, ht014b, ht124b, ht123c, hbg3a, hbg4c]
                            ·
                              linarith only [hdelta1, ht013b, ht014b, ht234d, hbg3c, hbg4c]
                            ·
                              linarith only [hdelta1, ht012b, ht014a, ht024a, ht123c, hbg1, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, ht013c, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, ht123a, hbg3c, hbg1]
                        ·
                          linarith only [hdelta1, ht012c, ht013b, hbg0a, hbg1]
                        ·
                          linarith only [hdelta1, ht012c, ht013b, hbg0a, hbg1]
                        ·
                          linarith only [hdelta1, ht012c, ht013b, hbg0a, hbg1]
                        ·
                          linarith only [hdelta1, ht013b, ht023c, hbg0a, hbg0b, hbg1]
                        ·
                          linarith only [hdelta1, ht013b, ht014c, ht023c, hbg0a, hbg1]
                        ·
                          linarith only [hdelta1, ht013b, ht024b, ht023c, hbg0a, hbg1]
                      ·
                        linarith only [hdelta1, h011, h230, ht014a, ht123b, hbg1c]
                      ·
                        have hb0 := m.budget 0 (by decide) 3 2 4 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, ht013b, ht024a, ht123b, ht234d, hbg0]
                        ·
                          linarith only [hdelta1, ht012b, ht024c, ht123b, ht234d, hbg1a, hbg0]
                        ·
                          linarith only [hdelta1, h011, h230, ht014b, ht124b, ht123b, hbg1a, hbg0]
                        ·
                          linarith only [hdelta1, ht024a, ht124b, ht123b, ht023c, ht234d, hbg1c, hbg0]
                        ·
                          linarith only [hdelta1, h011, h030, ht024c, ht124b, ht123b, ht234d, hbg1c, hbg0c]
                        ·
                          linarith only [hdelta1, ht013e, ht024b, hbg0c]
                        ·
                          linarith only [hdelta1, h130, h241, ht024a, ht124b, hbg1c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012e, hbg0c]
                        ·
                          linarith only [hdelta1, ht024c, ht124b, ht123b, ht023c, ht234d, hbg1c, hbg0c]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h021, h230, ht012b, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h011, h230, ht024b, ht123b, ht023c, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h230, h341, ht124b, ht123b, hbg3, hbg1c, hbg0b]
                          ·
                            linarith only [hdelta1, ht012b, ht034a, ht024b, ht123b, hbg3, hbg1a, hbg0c]
                          ·
                            linarith only [hdelta1, h011, h230, ht124b, hbg1c, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h230, ht124b, hbg1c, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h230, ht124b, hbg1c, hbg3a]
                          ·
                            have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc41, hc40, hc42, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, h011, h140, hbg4, hbg0a]
                            ·
                              linarith only [hdelta1, h130, h241, ht012b, ht024b, hbg1a, hbg4]
                            ·
                              linarith only [hdelta1, h230, h341, ht012b, ht024a, ht123b, hbg1a, hbg4]
                            ·
                              linarith only [hdelta1, ht014b, hbg0c, hbg4, hbg3b]
                            ·
                              linarith only [hdelta1, ht124b, ht123b, ht234d, hbg1a, hbg4c]
                            ·
                              linarith only [hdelta1, h230, h341, ht024a, ht124b, ht123b, ht023c, hbg1a, hbg0c, hbg4c]
                            ·
                              linarith only [hdelta1, hbg0c, hbg4c, hbg3b]
                            ·
                              linarith only [hdelta1, h230, h341, ht014b, ht124b, ht123b, hbg1a, hbg4c]
                            ·
                              linarith only [hdelta1, ht014b, ht123b, ht234d, hbg4c, hbg3c]
                            ·
                              linarith only [hdelta1, h011, h230, ht012b, ht024a, ht123b, hbg1c, hbg4c]
                          ·
                            linarith only [hdelta1, ht034a, ht123b, hbg3c]
                          ·
                            linarith only [hdelta1, ht012b, ht024b, ht123b, hbg1a, hbg0c, hbg3c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, h011, h230, ht123a, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123c, hbg1c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h230, ht124b, ht123c, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, ht024a, ht123b, ht023c, ht234d, hbg3]
                        ·
                          have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc41, hc40, hc42, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht014c, ht124b, ht123c, hbg1b, hbg4]
                          ·
                            linarith only [hdelta1, ht014b, ht124b, ht123a, ht234d, hbg4]
                          ·
                            linarith only [hdelta1, h230, h341, ht012b, ht024a, ht123a, hbg4]
                          ·
                            linarith only [hdelta1, ht013e, hbg3, hbg4, hbg1a]
                          ·
                            linarith only [hdelta1, h230, h241, ht124b, ht123a, hbg4c]
                          ·
                            linarith only [hdelta1, h230, h341, ht024c, ht124b, ht123a, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, hbg1c, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, h230, h341, ht014b, ht124b, ht123a, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, hbg1c, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, ht013b, hbg1c, hbg3, hbg4b]
                        ·
                          linarith only [hdelta1, ht012b, ht024a, ht123a, ht234c, hbg3]
                        ·
                          linarith only [hdelta1, ht024a, ht023c, ht234d, hbg3c]
                        ·
                          have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc41, hc40, hc42, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h041, h230, ht124b, ht123c, hbg4, hbg3a]
                          ·
                            linarith only [hdelta1, ht014b, ht124b, ht123c, hbg4, ht234d, hbg3a]
                          ·
                            linarith only [hdelta1, h230, h341, ht012b, ht024a, ht123c, hbg4, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, hbg4, hbg1c, hbg3b]
                          ·
                            linarith only [hdelta1, ht124b, ht123c, hbg4c, ht234d, hbg3a]
                          ·
                            linarith only [hdelta1, h230, h341, ht024c, ht124b, ht123c, hbg4c, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht024c, hbg4c, ht234d, hbg3c]
                          ·
                            linarith only [hdelta1, h230, h341, ht014b, ht124b, ht123c, hbg4c, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht014b, hbg4c, ht234d, hbg3c]
                          ·
                            linarith only [hdelta1, ht012b, ht024a, ht123c, hbg4c, hbg1c]
                        ·
                          linarith only [hdelta1, ht013b, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, h230, h341, ht124b, ht123a, hbg1c, hbg3c]
                        ·
                          linarith only [hdelta1, ht024a, ht124b, ht123a, ht023c, hbg1c, ht234c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht124b, ht123a, hbg1c, hbg3c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
                ·
                  linarith only [ht012b, ht024a, ht124a]
            ·
              linarith only [ht034c, ht024b, ht023c]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb0 := m.budget 0 (by decide) 3 4 2 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        linarith only [hdelta1, ht012d, ht023b, ht123a, hbg0, ht024c]
                      ·
                        linarith only [hdelta1, ht012d, ht024b, ht123a, ht234b, hbg0]
                      ·
                        linarith only [hdelta1, h011, h120, ht023a, ht123a, hbg0]
                      ·
                        have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, ht012d, ht023a, ht123c, hbg1]
                        ·
                          linarith only [hdelta1, ht012d, ht024a, ht124c, ht123b, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 2 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht023a, hbg3, ht123b]
                          ·
                            linarith only [hdelta1, h120, h341, ht123a, ht034a, hbg3]
                          ·
                            linarith only [hn, hdelta1, hbg0, ht134e, hbg3, hbg1]
                          ·
                            linarith only [hn, hdelta1, ht134b, ht034a, hbg0, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, ht012d, ht034b, ht024c, hbg3c, ht123b]
                          ·
                            linarith only [hdelta1, hbg0, ht134e, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht134b, ht034a, hbg0, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, hbg0, ht134e, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht134b, ht034a, hbg0, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, hbg0, ht134e, hbg3a, hbg1]
                        ·
                          linarith only [hdelta1, ht012c, ht023a, ht123a, hbg1]
                        ·
                          linarith only [hdelta1, h011, h120, ht012c, ht024a, ht124c, hbg1c]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 2 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h120, h231, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, ht012d, ht123a, ht023c, hbg3]
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, ht134b, ht034a, hbg0, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, h031, h120, hbg1a, hbg3c]
                          ·
                            linarith only [hdelta1, h120, h341, ht134b, hbg0, hbg3b, hbg1c]
                          ·
                            linarith only [hdelta1, ht012d, ht024a, ht134b, ht034a, ht234b, hbg0, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, h120, h341, ht134b, hbg0, hbg3b, hbg1c]
                          ·
                            linarith only [hdelta1, ht123c, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, h120, h341, ht134b, hbg0, hbg3a, hbg1c]
                        ·
                          linarith only [hdelta1, ht013a, hbg1c]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 2 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht023a, ht123b, hbg3]
                          ·
                            linarith only [hdelta1, h011, h120, ht013d, ht123a, hbg3, hbg1c]
                          ·
                            linarith only [hn, hdelta1, h120, h341, hbg0, ht123b, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht034a, hbg1a, hbg0, hbg1b, hbg3]
                          ·
                            linarith only [hdelta1, ht012d, ht034b, ht024c, ht123b, hbg3c]
                          ·
                            linarith only [hdelta1, h120, h341, hbg0, hbg3b, ht123b, hbg1c]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, hbg3b, hbg1c]
                          ·
                            linarith only [hdelta1, h120, h341, hbg0, hbg3b, ht123b, hbg1c]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, hbg3b, hbg1c]
                          ·
                            linarith only [hdelta1, h120, h341, hbg0, hbg3a, ht123b, hbg1c]
                        ·
                          linarith only [hdelta1, ht014a, ht123b, hbg1c]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 2 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht024a, hbg3, ht234b, ht123b, hbg1b]
                          ·
                            linarith only [hdelta1, ht012c, ht034b, ht123a, hbg3, ht024c, hbg1b]
                          ·
                            linarith only [hdelta1, ht023b, ht123a, hbg3, ht134e, hbg1c]
                          ·
                            linarith only [hdelta1, ht023b, ht134b, ht123a, hbg3, ht034a, hbg1c]
                          ·
                            linarith only [hdelta1, ht012c, ht034b, ht024c, hbg3c, ht123b, hbg1b]
                          ·
                            linarith only [hdelta1, ht023b, ht134e, hbg3c, ht123b, hbg1c]
                          ·
                            linarith only [hdelta1, ht023b, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, ht123a, ht134e, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, ht134b, ht123a, ht034a, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, ht023b, ht134b, ht123a, hbg3c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012d, ht023b, ht123a, hbg0c]
                      ·
                        linarith only [hdelta1, h011, h120, ht023b, ht123a, ht024c, hbg0c]
                      ·
                        have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, h041, h120, ht023b, ht123c, hbg1, hbg0a]
                        ·
                          linarith only [hdelta1, ht012d, ht024a, ht124c, hbg1, ht123b]
                        ·
                          have hb4 := m.budget 4 (by decide) 1 2 0 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc41, hc42, hc40, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht014d, ht024a, hbg0c, hbg4]
                          ·
                            linarith only [hdelta1, ht012d, ht024c, ht124a, hbg4]
                          ·
                            linarith only [hdelta1, h030, h341, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, ht034a, hbg1, hbg0b, hbg4]
                          ·
                            linarith only [hdelta1, ht012d, ht134b, hbg4c, ht024c, ht123b]
                          ·
                            linarith only [hdelta1, hbg1, ht134e, hbg0c, hbg4b]
                          ·
                            linarith only [hdelta1, ht034c, hbg1, hbg0c, hbg4b]
                          ·
                            linarith only [hdelta1, h120, h341, ht134b, hbg1, ht123b, hbg0c, hbg4b]
                          ·
                            linarith only [hdelta1, ht034c, hbg1, hbg0c, hbg4b]
                          ·
                            linarith only [hdelta1, hbg4a, hbg1, hbg0c, hbg4b]
                        ·
                          linarith only [hdelta1, ht012c, ht013b, ht024c, hbg1, hbg0a, ht123b]
                        ·
                          linarith only [hdelta1, ht012d, ht024a, ht124c, hbg1c]
                        ·
                          linarith only [hdelta1, ht012d, ht134b, hbg1c, ht024c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012c, ht023b, ht123c, hbg1c, ht024c, hbg0a]
                        ·
                          linarith only [hdelta1, ht012d, hbg1c, ht024c, ht123b, hbg0c]
                        ·
                          linarith only [hdelta1, ht014a, hbg1c, ht123b]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 2 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht023b, ht024c, hbg3, hbg0a, ht123b, hbg1b]
                          ·
                            linarith only [hdelta1, ht012c, ht123a, ht024c, hbg3, hbg0a, hbg1b]
                          ·
                            linarith only [hdelta1, ht023b, ht123a, hbg1c, hbg3, ht134e]
                          ·
                            linarith only [hdelta1, ht013b, ht034c, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht012c, hbg3c, ht024c, hbg0a, ht123b, hbg1b]
                          ·
                            linarith only [hdelta1, ht023b, hbg1c, hbg3c, ht134e, ht123b]
                          ·
                            linarith only [hdelta1, ht023b, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, h120, h341, ht123a, hbg3c]
                          ·
                            linarith only [hdelta1, ht034c, ht123c, hbg3c, hbg0a]
                          ·
                            linarith only [hdelta1, ht023b, ht134b, ht123a, hbg1c, hbg3c]
                      ·
                        linarith only [hdelta1, ht014e, hbg0c]
                      ·
                        have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, ht012d, ht013b, ht034b, hbg1, hbg0a]
                        ·
                          linarith only [hdelta1, h011, h130, ht012c, ht014b, hbg1, hbg0a]
                        ·
                          have hb4 := m.budget 4 (by decide) 1 2 0 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc41, hc42, hc40, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h011, h130, ht012c, ht134b, ht024b, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, h011, h240, ht012c, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, ht034b, hbg1, ht134e, hbg0b, hbg4]
                          ·
                            linarith only [hdelta1, ht034a, hbg1, hbg0b, hbg4]
                          ·
                            linarith only [hdelta1, ht012d, ht134b, ht123b, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, ht024b, ht134e, hbg4c]
                          ·
                            linarith only [hdelta1, ht012c, ht024b, ht034a, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, h120, h341, ht123a, ht234b, hbg4c]
                          ·
                            linarith only [hdelta1, ht012c, ht124c, ht034a, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht034b, hbg1, hbg0b, hbg4c]
                        ·
                          linarith only [hdelta1, ht012c, ht023a, ht123a, hbg1]
                        ·
                          linarith only [hdelta1, ht012d, ht024b, ht124c, hbg1c, hbg0a]
                        ·
                          linarith only [hdelta1, ht012d, ht134b, ht034b, hbg1c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012c, ht023b, ht034b, ht123c, hbg1c, hbg0a]
                        ·
                          linarith only [hdelta1, ht012d, ht034b, hbg1c, ht123b, hbg0c]
                        ·
                          linarith only [hdelta1, ht012c, ht024b, ht124c, hbg1c, ht123b, hbg0a]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 2 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht024b, ht234b, hbg1b, ht123b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht012c, ht034b, ht123a, hbg1b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht023b, ht123a, hbg1c, ht134e, hbg3]
                          ·
                            linarith only [hdelta1, ht023b, ht134b, ht123a, ht034a, hbg1c, hbg3]
                          ·
                            linarith only [hdelta1, ht012c, ht034b, hbg1b, ht123b, hbg3c, hbg0a]
                          ·
                            linarith only [hdelta1, ht023b, hbg1c, ht134e, ht123b, hbg3c]
                          ·
                            linarith only [hdelta1, ht023b, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, h120, h341, ht123a, hbg3c]
                          ·
                            linarith only [hdelta1, ht123c, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, ht023b, ht134b, ht123a, hbg1c, hbg3c]
                      ·
                        have hb3 := m.budget 3 (by decide) 1 2 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc32, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h120, ht024a, ht234b, hbg3, ht123b, hbg0a]
                        ·
                          linarith only [hdelta1, h011, h230, ht023c, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h120, h341, ht024a, ht123a, ht234b, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, ht024a, ht123c, ht034a, ht234b, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, h011, h120, ht034b, ht024c, ht123b, hbg3c, hbg0a]
                        ·
                          linarith only [hdelta1, h120, h341, ht024a, ht234b, hbg0c, ht123b, hbg3c]
                        ·
                          linarith only [hdelta1, ht024a, ht034a, ht234b, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, h120, h341, ht123a, hbg3c]
                        ·
                          linarith only [hdelta1, ht123c, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, ht024a, ht134b, ht124c, hbg0c, hbg3c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht023b, ht123c, ht034a, ht134a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht134b, ht123b, ht124c]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 2 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht024a, ht124a, ht123b, hbg1]
                      ·
                        linarith only [hdelta1, h011, h230, ht014a, ht123a, hbg1]
                      ·
                        have hb4 := m.budget 4 (by decide) 1 2 0 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc41, hc42, hc40, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht024a, ht123a, hbg4, ht124b]
                        ·
                          linarith only [hdelta1, h041, h230, ht123a, ht124a, hbg4]
                        ·
                          linarith only [hdelta1, h230, h341, ht024b, ht123a, ht124a, hbg4]
                        ·
                          have hb0 := m.budget 0 (by decide) 3 4 2 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hn, hdelta1, ht013e, ht034c, hbg4, hbg0, hbg1]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht024b, ht123a, ht124a, hbg0]
                          ·
                            linarith only [hdelta1, h011, h230, ht024a, ht123a, ht124a, hbg0]
                          ·
                            linarith only [hn, hdelta1, ht034a, hbg4, hbg0, hbg1]
                          ·
                            linarith only [hdelta1, ht013e, ht034c, hbg4, hbg0a, hbg1]
                          ·
                            linarith only [hdelta1, ht013e, ht034c, hbg4, hbg0a, hbg1]
                          ·
                            linarith only [hdelta1, ht034a, hbg0b, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, ht013e, ht014b, ht034a, hbg4, hbg0c]
                          ·
                            linarith only [hdelta1, ht034a, hbg0b, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, ht034a, hbg0b, hbg4, hbg1]
                        ·
                          linarith only [hdelta1, h041, h230, ht123a, hbg4c, ht124b]
                        ·
                          linarith only [hdelta1, h230, h341, ht024b, ht123a, hbg4c, ht124b]
                        ·
                          have hb0 := m.budget 0 (by decide) 3 4 2 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, ht013e, ht034c, hbg0, hbg4b, hbg1]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht024b, ht123a, hbg0, ht124b, hbg4a]
                          ·
                            linarith only [hdelta1, h011, h230, ht024a, ht123a, hbg0, ht124b, hbg4a]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, hbg4b, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht013e, hbg0c]
                          ·
                            linarith only [hdelta1, ht013e, ht024c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012c, ht024a, ht034c, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, h011, h230, ht014b, ht123a, ht124b, hbg0c]
                          ·
                            linarith only [hdelta1, ht012c, ht024b, ht034a, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht024a, ht034a, hbg4c, hbg0c]
                        ·
                          linarith only [hdelta1, h230, h341, ht123a, hbg4c, ht124a]
                        ·
                          linarith only [hdelta1, h011, h230, ht034c, ht123a, hbg4c, ht124a, hbg1]
                        ·
                          linarith only [hdelta1, h011, h230, ht024b, ht123a, hbg4c, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, ht012c, ht024a, ht123c, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht024a, ht124c, ht123b, hbg1c]
                      ·
                        have hb4 := m.budget 4 (by decide) 1 2 0 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc41, hc42, hc40, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h021, h230, ht024a, hbg1a, hbg4, ht123b, ht124b]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, hbg1a, ht024c, ht124a, hbg4, ht123b]
                        ·
                          linarith only [hdelta1, h230, h341, ht014b, hbg1a, hbg4, ht123b, ht124b]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h230, hbg1c, ht124b, hbg3]
                          ·
                            linarith only [hdelta1, h011, h230, ht034a, hbg1b, hbg4, ht123b, hbg3]
                          ·
                            linarith only [hdelta1, ht013e, hbg1b, hbg4, hbg3]
                          ·
                            linarith only [hdelta1, ht014b, ht034c, hbg1a, ht123b, ht124b, hbg3]
                          ·
                            linarith only [hdelta1, h011, h230, hbg3a, hbg1c, ht124b]
                          ·
                            linarith only [hdelta1, h011, h230, hbg3a, hbg1c, ht124b]
                          ·
                            linarith only [hdelta1, h011, h230, hbg3a, hbg1c, ht124b]
                          ·
                            linarith only [hdelta1, h011, h130, hbg1b, hbg3c, hbg4]
                          ·
                            linarith only [hdelta1, ht034a, hbg3c, ht123b]
                          ·
                            linarith only [hdelta1, ht013e, hbg3c, ht123b, hbg1c, ht124b]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, hbg1a, ht024c, hbg4c, ht123b, ht124b]
                        ·
                          linarith only [hdelta1, h230, h341, ht024b, hbg1a, hbg4c, ht123b, ht124b]
                        ·
                          have hb0 := m.budget 0 (by decide) 3 4 2 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht013e, ht024a, ht034c, hbg0, hbg4c]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht014b, hbg1a, hbg0, ht123b, ht124b]
                          ·
                            linarith only [hdelta1, h011, h230, ht024a, hbg1a, hbg0, hbg4a, ht123b, ht124b]
                          ·
                            linarith only [hdelta1, ht012c, ht024a, ht034a, hbg0, hbg4c]
                          ·
                            linarith only [hdelta1, ht012c, ht013e, hbg0c]
                          ·
                            linarith only [hdelta1, ht013e, hbg0c, ht024c]
                          ·
                            linarith only [hdelta1, ht012c, ht024a, ht034c, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, h011, h230, ht024b, hbg1a, hbg0c, hbg4a, ht123b, ht124b]
                          ·
                            linarith only [hdelta1, ht012c, ht024b, ht034a, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht024a, ht034a, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, h230, h341, hbg1a, ht124a, hbg4c, ht123b]
                        ·
                          linarith only [hdelta1, h011, h230, ht034c, ht124a, hbg4c, ht123b, hbg1c]
                        ·
                          linarith only [hdelta1, h011, h230, ht024b, ht124a, hbg4c, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012c, ht024a, ht124a, hbg1c]
                      ·
                        linarith only [hdelta1, h011, h230, ht123a, hbg1c]
                      ·
                        linarith only [hdelta1, ht012c, ht024a, ht123c, ht124c, hbg1c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h021, h230, ht024a, ht123c, ht124a, hbg3]
                        ·
                          linarith only [hdelta1, ht013c, hbg1b, hbg3]
                        ·
                          have hb4 := m.budget 4 (by decide) 1 2 0 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc41, hc42, hc40, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht024a, ht123a, ht124b, hbg4]
                          ·
                            linarith only [hdelta1, ht012c, ht123c, ht024c, hbg1b, ht124a, hbg4]
                          ·
                            linarith only [hdelta1, h230, h341, ht024b, ht123a, ht124a, hbg4]
                          ·
                            linarith only [hdelta1, ht013b, hbg1a, hbg1b, hbg4, hbg3]
                          ·
                            linarith only [hdelta1, ht012c, ht123c, ht024c, hbg1b, ht124b, hbg4c]
                          ·
                            linarith only [hdelta1, h230, h341, ht024b, ht123a, ht124b, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, hbg4b, hbg1c, hbg3]
                          ·
                            linarith only [hdelta1, h230, h341, ht123a, ht124a, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, hbg4b, hbg1c, hbg3]
                          ·
                            linarith only [hdelta1, ht013b, hbg4b, hbg1c, hbg3]
                        ·
                          linarith only [hdelta1, ht013b, ht123a, ht034a, hbg1c, ht124b, hbg3]
                        ·
                          linarith only [hdelta1, h230, h341, ht034a, hbg3c]
                        ·
                          have hb4 := m.budget 4 (by decide) 1 2 0 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc41, hc42, hc40, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h021, h230, ht024a, ht123c, hbg3a, hbg4, ht124b]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht123c, ht024c, ht124a, hbg3a, hbg4]
                          ·
                            linarith only [hdelta1, h230, h341, ht014b, ht123c, hbg3a, hbg4, ht124b]
                          ·
                            linarith only [hdelta1, ht013b, hbg4, hbg1c, hbg3b]
                          ·
                            linarith only [hdelta1, h041, h230, ht123c, hbg3a, ht124b, hbg4c]
                          ·
                            linarith only [hdelta1, h230, h341, ht024b, ht123c, hbg3a, ht124b, hbg4c]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht013b, ht024a, hbg3c, hbg4c]
                          ·
                            linarith only [hdelta1, h230, h341, ht123c, ht124a, hbg3a, hbg4c]
                          ·
                            linarith only [hdelta1, ht034c, ht123c, ht124a, hbg1c, hbg4c]
                          ·
                            linarith only [hdelta1, ht024b, ht123c, ht124a, hbg1c, hbg4c]
                        ·
                          linarith only [hdelta1, ht013b, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, h230, h341, ht123a, hbg3c, hbg1c, ht124b]
                        ·
                          linarith only [hdelta1, ht123a, ht034a, hbg3c, hbg1c, ht124b]
                        ·
                          linarith only [hdelta1, ht013b, ht123a, hbg3c, hbg1c, ht124b]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb0 := m.budget 0 (by decide) 3 4 2 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hn, hdelta1, h021, h230, ht013b, hbg0, ht024c, hbg3]
                        ·
                          linarith only [hn, hdelta1, h011, h130, ht012c, hbg0, ht024c, hbg3]
                        ·
                          have hb1 := m.budget 1 (by decide) 3 4 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            have hb4 := m.budget 4 (by decide) 2 1 0 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc42, hc41, hc40, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, ht013e, ht014a, ht024d, hbg0, hbg4]
                            ·
                              linarith only [hn, hdelta1, h041, h230, hbg1, hbg4, ht123b]
                            ·
                              linarith only [hn, hdelta1, h230, h341, ht014b, hbg1, hbg4, ht123b]
                            ·
                              linarith only [hdelta1, ht012a, ht013e, ht034c, hbg0, ht124a, hbg4]
                            ·
                              linarith only [hdelta1, h041, h230, hbg1, ht123b, hbg4b]
                            ·
                              linarith only [hdelta1, h230, h341, ht014b, hbg1, ht123b, hbg4b]
                            ·
                              linarith only [hdelta1, ht012a, ht013e, ht034c, hbg0, ht124c, hbg4c]
                            ·
                              linarith only [hdelta1, h030, h341, hbg0, hbg4b]
                            ·
                              linarith only [hdelta1, h011, h230, ht012c, hbg1, ht024c, ht123b, hbg4a]
                            ·
                              linarith only [hdelta1, h030, h341, hbg0, hbg4a]
                          ·
                            linarith only [hdelta1, ht012a, ht013e, ht014d, hbg1, hbg0]
                          ·
                            linarith only [hdelta1, ht013e, ht034c, hbg1, hbg0, ht124a, ht234e]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, ht034c, hbg1, hbg0, ht124a, ht234e]
                          ·
                            linarith only [hdelta1, h011, h230, ht012a, ht123b, hbg1c]
                          ·
                            have hb4 := m.budget 4 (by decide) 2 1 0 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc42, hc41, hc40, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, h011, h240, hbg4, ht124c, hbg1b]
                            ·
                              linarith only [hdelta1, h041, h230, hbg4, ht123b, hbg1a]
                            ·
                              linarith only [hdelta1, h230, h341, ht014b, hbg4, ht123b, hbg1a]
                            ·
                              linarith only [hdelta1, ht013e, ht034c, hbg0, hbg4, ht124a, hbg1b]
                            ·
                              linarith only [hdelta1, ht034c, hbg4c, ht234e]
                            ·
                              linarith only [hdelta1, h230, h341, ht013e, hbg0, ht124c, hbg4b, ht123b, hbg1c]
                            ·
                              linarith only [hdelta1, ht013e, ht034c, hbg0, ht124c, hbg1b, hbg4c]
                            ·
                              linarith only [hdelta1, h030, h341, hbg0, hbg4b]
                            ·
                              linarith only [hdelta1, h011, h230, ht034c, ht124a, ht123b, hbg4c, hbg1c]
                            ·
                              linarith only [hdelta1, h030, h341, hbg0, hbg4a]
                          ·
                            linarith only [hdelta1, ht013b, ht014c, hbg0, hbg1b]
                          ·
                            linarith only [hdelta1, ht013e, ht034c, ht124b, hbg0, ht234e, hbg1c]
                          ·
                            linarith only [hdelta1, ht013b, ht014c, hbg0, hbg1b]
                          ·
                            linarith only [hdelta1, ht012c, ht013b, hbg0, ht024c, hbg1b]
                        ·
                          linarith only [hn, hdelta1, ht023b, ht034c, hbg0, hbg3]
                        ·
                          linarith only [hdelta1, h011, h130, ht012c, hbg0, ht024c, hbg3b]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht013b, hbg0, ht024c, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht013b, hbg0, ht024c, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h130, ht012c, hbg0, ht024c, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h130, ht012c, hbg0, ht024c, hbg3a]
                        ·
                          linarith only [hdelta1, ht013b, ht034c, hbg0, hbg3b, ht123b]
                      ·
                        have hb1 := m.budget 1 (by decide) 3 4 2 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hn, hdelta1, h011, h230, ht012c, ht014b, hbg0, hbg1, ht123b]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h230, ht012a, ht134b, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, h011, h130, ht012a, ht034a, ht124b, hbg3, ht234e, hbg1]
                          ·
                            linarith only [hdelta1, ht012a, ht013e, ht124b, hbg3, ht234e, hbg1]
                          ·
                            linarith only [hdelta1, ht012a, ht013e, ht034a, ht134b, hbg3, hbg1, ht123b]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht034b, hbg0, hbg3a, hbg3b]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht013b, ht034b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht013b, ht034b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h130, ht012c, ht034b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h130, ht012c, ht034b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht012a, ht013e, ht134b, hbg1, ht123b, hbg3c]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h021, h230, ht013b, ht034b, hbg0, hbg3]
                          ·
                            linarith only [hn, hdelta1, h011, h130, ht012c, ht034b, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht013e, ht124a, ht234e, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht013e, ht123a, ht034a, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht034b, hbg0, hbg3b, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht013b, ht034b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht013b, ht034b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h130, ht012c, ht034b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h130, ht012c, ht034b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht013e, ht234b, ht124a, hbg1, hbg3c]
                        ·
                          linarith only [hn, hdelta1, ht012c, ht014b, hbg0, ht134b, hbg1]
                        ·
                          linarith only [hdelta1, h011, h130, ht012c, ht014b, hbg0, hbg1a]
                        ·
                          linarith only [hdelta1, h011, h130, ht012c, ht014b, hbg0, hbg1a]
                        ·
                          linarith only [hdelta1, h011, h130, ht012c, ht014b, hbg0, hbg1a]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h230, ht123c, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, h011, h130, ht034a, ht124b, hbg3, hbg1c, ht234e]
                          ·
                            linarith only [hdelta1, ht013e, ht124b, hbg3, hbg1c, ht234e]
                          ·
                            linarith only [hdelta1, ht013e, ht034a, hbg3, ht134b, hbg1c, ht123b]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht034b, hbg0, hbg3b, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht013b, ht034b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht013b, ht034b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h130, ht012c, ht034b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h130, ht012c, ht034b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht013e, ht134b, hbg1c, hbg3c, ht123b]
                        ·
                          linarith only [hdelta1, ht012c, ht014b, hbg0, hbg1b, ht134b]
                        ·
                          linarith only [hdelta1, ht012c, ht014b, hbg0, hbg1b, ht134b]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hn, hdelta1, h011, h230, ht013b, ht023c, hbg0, hbg3]
                        ·
                          linarith only [hn, hdelta1, h011, h130, ht034b, hbg0, ht024c, hbg3]
                        ·
                          linarith only [hdelta1, ht012b, ht013e, hbg0, ht124a, hbg3, ht234e]
                        ·
                          linarith only [hdelta1, ht013e, ht023a, ht034a, hbg0, hbg3]
                        ·
                          linarith only [hdelta1, h011, h230, ht023c, hbg3b, hbg0, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h230, ht013b, ht023c, hbg0, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h230, ht013b, ht023c, hbg0, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h130, ht023c, hbg0, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h130, ht023c, hbg0, hbg3a]
                        ·
                          linarith only [hdelta1, ht012b, ht013e, hbg0, ht234b, hbg3c, ht124a]
                      ·
                        have hb4 := m.budget 4 (by decide) 2 1 0 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc42, hc41, hc40, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht012a, ht034a, hbg0, ht124c, hbg4, ht234e]
                        ·
                          have hb1 := m.budget 1 (by decide) 3 4 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h130, ht012c, ht024c, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, ht012a, ht134e, ht034a, hbg0, hbg1]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, ht124a, ht234e, hbg1]
                          ·
                            linarith only [hn, hdelta1, ht014c, ht134b, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, h130, h341, ht034c, hbg4, hbg1a]
                          ·
                            linarith only [hdelta1, h130, h341, ht034c, hbg4, hbg1a]
                          ·
                            linarith only [hdelta1, h130, h341, ht034c, hbg4, hbg1a]
                          ·
                            linarith only [hdelta1, ht034a, ht124b, hbg0, ht234e, hbg1c]
                          ·
                            linarith only [hdelta1, ht012c, ht024c, ht134b, hbg4, hbg1b]
                          ·
                            linarith only [hdelta1, ht012c, ht024c, ht134b, hbg4, hbg1b]
                        ·
                          linarith only [hdelta1, ht012a, ht034b, hbg0, ht124a, hbg4, ht234e]
                        ·
                          linarith only [hdelta1, ht012a, ht034a, hbg0, ht124a, hbg4]
                        ·
                          linarith only [hdelta1, ht024d, hbg4c]
                        ·
                          linarith only [hdelta1, ht014a, ht034b, hbg4c, hbg0, ht234e]
                        ·
                          linarith only [hdelta1, ht012a, ht034a, hbg4c, hbg0, ht124c]
                        ·
                          linarith only [hdelta1, ht134e, hbg4c]
                        ·
                          have hb1 := m.budget 1 (by decide) 3 4 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h011, h130, ht012c, ht024c, hbg1, hbg4a]
                          ·
                            linarith only [hdelta1, ht012a, ht134e, ht034a, hbg0, hbg1]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, ht124a, hbg1, hbg4b]
                          ·
                            linarith only [hdelta1, ht014c, ht134b, hbg1, hbg4a]
                          ·
                            linarith only [hdelta1, h011, h230, ht012a, hbg1c, ht123b]
                          ·
                            linarith only [hdelta1, h011, h230, ht034c, hbg4c, hbg1c, ht124a, ht123b]
                          ·
                            linarith only [hdelta1, ht012c, hbg1c, ht024c, hbg4a]
                          ·
                            linarith only [hdelta1, ht134e, ht034a, hbg1c, hbg0]
                          ·
                            linarith only [hdelta1, ht012a, hbg1c, ht134b]
                          ·
                            linarith only [hdelta1, ht034c, hbg4c, hbg1c, ht134b, ht124a]
                        ·
                          linarith only [hdelta1, ht012a, ht034b, hbg4c, hbg0, ht124a]
                      ·
                        linarith only [hdelta1, ht012c, ht013e, hbg0c]
                      ·
                        linarith only [hdelta1, ht013e, hbg0c, ht024c]
                      ·
                        have hb4 := m.budget 4 (by decide) 2 1 0 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc42, hc41, hc40, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht014a, ht024d, hbg0c, hbg4]
                        ·
                          have hb1 := m.budget 1 (by decide) 3 4 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h011, h130, ht012c, hbg4, ht024c, hbg0a, hbg1, hbg0b]
                          ·
                            linarith only [hdelta1, ht012a, ht034c, ht124b, hbg0c, ht234e, hbg1]
                          ·
                            linarith only [hdelta1, ht034c, hbg0c, ht124a, ht234e, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht013b, ht024c, hbg0a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, hbg4, ht024c, hbg1a, ht123b]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, hbg4, ht024c, hbg1a, ht123b]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, hbg4, ht024c, hbg1a, ht123b]
                          ·
                            linarith only [hdelta1, ht034c, ht124b, hbg0c, ht234e, hbg1c]
                          ·
                            linarith only [hdelta1, ht014c, hbg4, ht134b, hbg1b]
                          ·
                            linarith only [hdelta1, ht012c, hbg4, ht024c, ht134b, hbg1b]
                        ·
                          linarith only [hdelta1, h030, h341, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, ht012a, ht034c, hbg0c, hbg4, ht124a]
                        ·
                          linarith only [hdelta1, ht024d, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, ht234e, hbg4c]
                        ·
                          linarith only [hdelta1, ht012a, ht034c, hbg0c, ht124c, hbg4c]
                        ·
                          linarith only [hdelta1, ht134e, hbg4c]
                        ·
                          have hb1 := m.budget 1 (by decide) 3 4 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h011, h130, ht012c, ht024c, hbg1, hbg4a]
                          ·
                            linarith only [hdelta1, ht012a, ht034c, ht124b, hbg0c, hbg1, hbg4b]
                          ·
                            linarith only [hdelta1, ht034c, hbg0c, hbg1, ht124a, hbg4b]
                          ·
                            linarith only [hdelta1, ht012c, ht013b, ht024c, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, h011, h230, ht012a, hbg1c, ht123b]
                          ·
                            linarith only [hdelta1, h011, h230, ht034c, ht124a, hbg1c, hbg4c, ht123b]
                          ·
                            linarith only [hdelta1, ht012a, ht034c, ht124a, hbg1c, hbg4c]
                          ·
                            linarith only [hdelta1, ht034c, ht124b, hbg0c, hbg1c, hbg4b]
                          ·
                            linarith only [hdelta1, ht012a, ht134b, hbg1c]
                          ·
                            linarith only [hdelta1, ht034c, ht134b, ht124a, hbg1c, hbg4c]
                        ·
                          linarith only [hdelta1, ht012a, hbg0c, ht124a, hbg4c]
                      ·
                        linarith only [hdelta1, ht014e, hbg0c]
                      ·
                        have hb4 := m.budget 4 (by decide) 2 1 0 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc42, hc41, hc40, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h011, h240, ht012c, ht014b, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h011, h140, ht012c, hbg4, hbg0a]
                        ·
                          have hb1 := m.budget 1 (by decide) 3 4 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h130, h341, ht014a, ht034b, hbg0b, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, h140, h341, ht012a, ht034b, hbg0b, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, h230, h341, ht034b, ht123a, hbg0b, hbg4, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht013b, ht034b, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, h130, h341, ht014b, hbg4, hbg1a]
                          ·
                            linarith only [hdelta1, h130, h341, ht014b, hbg4, hbg1a]
                          ·
                            linarith only [hdelta1, h130, h341, ht014b, hbg4, hbg1a]
                          ·
                            linarith only [hdelta1, h140, h341, ht034b, hbg0b, hbg4, hbg1c]
                          ·
                            linarith only [hdelta1, ht012a, hbg1c, ht134b]
                          ·
                            linarith only [hdelta1, ht013b, ht034b, hbg4, hbg1c, ht124a, ht234e]
                        ·
                          have hb1 := m.budget 1 (by decide) 3 4 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, ht014b, hbg1, ht123b, hbg0a]
                          ·
                            linarith only [hdelta1, ht012a, hbg1, ht034a, ht124b, hbg0b, hbg4]
                          ·
                            linarith only [hdelta1, hbg1, ht034a, hbg0b, hbg4, ht124a]
                          ·
                            linarith only [hdelta1, ht012c, ht013b, ht034b, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, h011, h230, ht012a, hbg1c, ht123b]
                          ·
                            have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc32, hc31, hc30] at hb3
                            rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                              ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                              ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                            ·
                              linarith only [hn, hdelta1, h011, h230, ht012c, ht014b, ht034a, hbg0c, hbg4, hbg3, ht124a, hbg1c]
                            ·
                              linarith only [hdelta1, h011, h130, ht034a, hbg4, hbg3, ht124a, hbg1b]
                            ·
                              linarith only [hdelta1, hbg0b, hbg4, hbg3, ht124a, hbg1b]
                            ·
                              linarith only [hdelta1, ht012c, ht014b, ht034a, hbg0c, hbg3, hbg1a, ht123b]
                            ·
                              linarith only [hdelta1, h011, h230, ht012c, ht014b, ht034a, hbg0c, hbg4, ht124a, hbg1c, hbg3a]
                            ·
                              linarith only [hdelta1, ht012c, ht024b, hbg0c, hbg4, hbg3b]
                            ·
                              linarith only [hdelta1, h011, h230, ht012c, ht014b, ht034a, hbg0c, hbg4, ht124a, hbg1c, hbg3a]
                            ·
                              linarith only [hdelta1, h011, h130, ht012c, ht014b, hbg0c, hbg4, ht124a, hbg1c, hbg3b]
                            ·
                              linarith only [hdelta1, ht034a, ht123b, hbg3c]
                            ·
                              linarith only [hdelta1, h011, h230, ht012c, ht014b, hbg0c, hbg4, ht124a, hbg1c, ht123b, hbg3a]
                          ·
                            linarith only [hdelta1, ht012c, ht014b, hbg1c, hbg0a]
                          ·
                            linarith only [hdelta1, ht034a, ht124b, hbg0b, hbg4, hbg1c]
                          ·
                            linarith only [hdelta1, ht012a, ht134b, hbg1c]
                          ·
                            linarith only [hdelta1, ht013b, ht034a, hbg4, ht124a, hbg1c]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht234b, hbg4c, hbg0a]
                        ·
                          linarith only [hdelta1, ht014b, hbg4c, ht234e]
                        ·
                          linarith only [hdelta1, ht012c, ht014b, ht034a, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht134e, hbg4c]
                        ·
                          linarith only [hdelta1, ht012c, ht034a, ht124b, hbg0c, hbg4c]
                        ·
                          have hb1 := m.budget 1 (by decide) 3 4 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h011, h130, ht012c, ht014b, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, ht012a, ht034b, ht124b, hbg0b, hbg4c, hbg1]
                          ·
                            linarith only [hdelta1, ht034b, hbg0b, hbg4c, ht124a, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht013b, ht034b, hbg1, hbg0a]
                          ·
                            linarith only [hdelta1, h011, h230, ht012a, hbg1c, ht123b]
                          ·
                            linarith only [hdelta1, h011, h230, ht014b, hbg4c, hbg1c, ht124a, ht123b]
                          ·
                            linarith only [hdelta1, ht012c, ht014b, hbg1c, hbg0a]
                          ·
                            linarith only [hdelta1, ht034b, ht124b, hbg0b, hbg4c, hbg1c]
                          ·
                            linarith only [hdelta1, ht012a, ht134b, hbg1c]
                          ·
                            linarith only [hdelta1, ht013b, ht034b, hbg4c, hbg1c, ht124a]
                      ·
                        have hb4 := m.budget 4 (by decide) 2 1 0 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc42, hc41, hc40, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h011, h230, ht014b, hbg0a, ht234b, hbg4, ht024c]
                        ·
                          linarith only [hdelta1, h011, h140, hbg0a, hbg4, ht024c]
                        ·
                          linarith only [hdelta1, ht012b, ht034b, hbg4, ht124a, ht234e, hbg0c]
                        ·
                          linarith only [hdelta1, ht012b, ht034a, hbg4, ht124a, hbg0c]
                        ·
                          linarith only [hdelta1, h011, h230, hbg0a, ht234b, ht024c, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, ht234e, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, ht034a, ht024c, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht134e, hbg4c]
                        ·
                          linarith only [hdelta1, ht034a, ht124b, ht024c, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht024a, ht034b, hbg0c, hbg4c]
                    ·
                      linarith only [ht013b, ht034a, ht234a, ht123b]
                  ·
                    linarith only [ht013b, ht134a, ht034a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 1 2 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc31, hc32, hc30] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht012d, ht023a, ht123b, hbg3]
                      ·
                        linarith only [hdelta1, ht012d, ht123a, ht034a, ht023c, hbg3]
                      ·
                        linarith only [hdelta1, ht012d, ht123a, ht234a, ht023c, hbg3]
                      ·
                        linarith only [hdelta1, ht234a, ht034a, ht123c, hbg3]
                      ·
                        linarith only [hdelta1, ht012d, ht034a, ht123b, ht023c, hbg3c]
                      ·
                        linarith only [hdelta1, ht012d, ht234a, ht123b, ht023c, hbg3c]
                      ·
                        linarith only [hdelta1, ht234a, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023d, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, hbg3c, ht123c]
                      ·
                        linarith only [hdelta1, ht134a, hbg3c]
                    ·
                      have hb3 := m.budget 3 (by decide) 1 4 2 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc31, hc32, hc30] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht012d, ht023a, ht123b, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, ht012d, ht023a, ht134a, ht123b, hbg3]
                      ·
                        linarith only [hdelta1, ht012d, ht134a, ht123b, ht023c, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, ht023b, ht134a, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, ht012d, ht023a, ht123b, hbg3c]
                      ·
                        linarith only [hdelta1, ht012d, ht123b, ht023c, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht023b, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht012d, ht134c, ht023c, hbg3c, ht124b]
                      ·
                        linarith only [hdelta1, ht023b, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht134a, hbg3c, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht134a, ht123c, ht234a]
                    ·
                      have hb0 := m.budget 0 (by decide) 4 3 2 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        linarith only [hdelta1, ht012d, ht024b, ht023c, ht124a, hbg0]
                      ·
                        linarith only [hdelta1, ht012d, ht024b, ht124a, hbg0, ht034c]
                      ·
                        linarith only [hdelta1, h011, h340, ht023a, ht134a, ht123c, hbg0]
                      ·
                        have hb1 := m.budget 1 (by decide) 2 4 3 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, ht012d, ht024a, hbg1, ht124c]
                        ·
                          linarith only [hdelta1, ht012d, ht023a, hbg1, ht123c, ht124b]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h340, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, h021, h340, ht023a, ht134a, hbg3]
                          ·
                            linarith only [hdelta1, ht012d, ht123a, ht023c, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht134a, hbg1, hbg0, ht034c, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h340, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h340, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht012d, ht023c, ht134c, ht124b, hbg3c]
                          ·
                            linarith only [hdelta1, ht134a, hbg1, hbg3b, hbg0, ht034c]
                          ·
                            linarith only [hdelta1, ht134a, hbg1, hbg3b, hbg0, ht034c]
                        ·
                          linarith only [hdelta1, ht012c, ht023a, ht123a, hbg1]
                        ·
                          linarith only [hdelta1, h011, h120, ht013a, hbg1c]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h340, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, h021, h120, ht023a, hbg1a, hbg3, ht134c]
                          ·
                            linarith only [hdelta1, ht012d, ht123a, ht023c, hbg3]
                          ·
                            linarith only [hdelta1, ht134a, hbg3, hbg0, ht034c, hbg1b]
                          ·
                            linarith only [hdelta1, h021, h340, ht023a, hbg3c]
                          ·
                            linarith only [hdelta1, h011, h340, ht012d, hbg3c, ht023c, ht123c, ht134c, hbg1c]
                          ·
                            linarith only [hdelta1, hbg3c, hbg0, ht034c, hbg1b]
                          ·
                            linarith only [hdelta1, ht012d, hbg3c, ht023c, hbg1a, ht134c]
                          ·
                            linarith only [hdelta1, ht023b, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, ht134a, hbg3c, ht123c]
                        ·
                          linarith only [hdelta1, ht013a, ht134c, hbg1c]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h340, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, ht012d, ht023a, hbg1a, hbg3, ht124b]
                          ·
                            linarith only [hdelta1, ht012d, ht123a, ht023c, hbg3]
                          ·
                            linarith only [hdelta1, ht134a, hbg3, hbg0, ht034c, hbg1b]
                          ·
                            linarith only [hdelta1, h011, h340, ht012d, ht023a, hbg1c, ht124b, hbg3c]
                          ·
                            linarith only [hdelta1, h011, h340, ht012d, ht023c, ht123c, hbg1c, ht124b, hbg3c]
                          ·
                            linarith only [hdelta1, ht134b, hbg0, ht034c, hbg1c, hbg3b]
                          ·
                            linarith only [hdelta1, h031, h120, hbg3c, hbg1a, ht124b]
                          ·
                            linarith only [hdelta1, hbg3b, ht134b, hbg0, ht034c, hbg1c]
                          ·
                            linarith only [hdelta1, hbg3b, ht134b, hbg0, ht034c, hbg1c]
                        ·
                          linarith only [hdelta1, ht013a, hbg1c, ht124b]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h340, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, ht012c, ht023a, hbg1b, ht134c, ht124b, hbg3]
                          ·
                            linarith only [hdelta1, ht012c, ht123a, ht023c, hbg1b, hbg3]
                          ·
                            linarith only [hdelta1, ht134a, hbg0, ht034c, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, ht012c, ht023a, hbg3c]
                          ·
                            linarith only [hdelta1, h011, h340, ht012c, ht023c, ht234c, ht124a, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht023b, ht234c, ht124a, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht013d, hbg3c]
                          ·
                            linarith only [hdelta1, ht023b, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, ht134a, ht123c, hbg3c]
                      ·
                        linarith only [hdelta1, ht012d, ht024b, ht124a, hbg0c]
                      ·
                        linarith only [hdelta1, h011, h120, ht024b, ht023c, ht124a, hbg0c]
                      ·
                        have hb1 := m.budget 1 (by decide) 2 4 3 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, ht012d, ht014b, ht023c, hbg0a, hbg1]
                        ·
                          linarith only [hdelta1, ht012d, ht023a, ht123c, ht124b, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h340, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht023a, ht013d, hbg3, hbg0c]
                          ·
                            linarith only [hdelta1, ht012d, ht123a, ht023c, hbg3]
                          ·
                            linarith only [hdelta1, ht134a, hbg3, hbg0a, hbg0b, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, ht012c, ht134a, ht023c, hbg3c]
                          ·
                            linarith only [hdelta1, ht134a, hbg3b, hbg1, hbg0c]
                          ·
                            linarith only [hdelta1, ht134a, hbg3b, hbg1, hbg0c]
                        ·
                          linarith only [hdelta1, ht012c, ht014b, ht023c, hbg0a, ht124b, hbg1]
                        ·
                          linarith only [hdelta1, ht012d, ht023a, ht123c, hbg1c]
                        ·
                          linarith only [hdelta1, ht012d, ht023c, ht134c, hbg1c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012c, ht024b, ht023c, hbg1c, ht124c, hbg0a]
                        ·
                          linarith only [hdelta1, ht012d, ht023c, hbg1c, ht124b, hbg0c]
                        ·
                          linarith only [hdelta1, ht013a, hbg1c, ht124b]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h340, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, ht012c, ht023a, ht123b, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, ht012c, ht123a, ht023c, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, ht024b, ht134a, hbg1c, ht124a, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, ht012c, ht023a, hbg3c]
                          ·
                            linarith only [hdelta1, h011, h340, ht012c, ht023c, ht234c, hbg1c, ht124a, hbg3c]
                          ·
                            linarith only [hdelta1, ht024b, hbg1c, ht124a, hbg0a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013d, hbg3c]
                          ·
                            linarith only [hdelta1, ht023b, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, ht123a, ht134a, hbg1c, hbg3c]
                      ·
                        linarith only [hdelta1, h011, h340, ht023b, ht134a, ht123c, hbg0c]
                      ·
                        have hb1 := m.budget 1 (by decide) 2 4 3 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, ht012d, ht014b, hbg0a, ht034c, hbg1]
                        ·
                          linarith only [hdelta1, h011, h140, ht012c, ht023b, hbg0a, ht123c, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h340, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, h021, h130, ht023b, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, ht134a, ht034c, hbg1, hbg0b, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h340, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h340, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h340, ht012c, ht134a, hbg0a, hbg3c]
                          ·
                            linarith only [hdelta1, ht023b, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, ht134a, ht123c, hbg3c]
                        ·
                          linarith only [hdelta1, ht012c, ht023a, ht234c, ht124a, hbg1]
                        ·
                          linarith only [hdelta1, ht012d, ht023b, hbg0a, ht123c, hbg1c]
                        ·
                          linarith only [hdelta1, ht012d, ht134c, hbg1c, ht034c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012c, ht023b, hbg0a, ht234c, hbg1c, ht124c]
                        ·
                          linarith only [hdelta1, ht012d, hbg1c, ht034c, ht124b, hbg0c]
                        ·
                          linarith only [hdelta1, ht012c, ht023b, hbg0a, ht123c, hbg1c, ht124b]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc32, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h340, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, h011, h130, ht012c, ht023b, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, h011, h230, ht012c, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, ht024b, ht134a, ht124a, hbg1c, ht034c, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, ht012c, ht023b, hbg3c, hbg0a]
                          ·
                            linarith only [hdelta1, h011, h340, ht012c, hbg3c, hbg0a, ht123c]
                          ·
                            linarith only [hdelta1, ht023b, hbg3c, ht234c, ht124a, hbg1c]
                          ·
                            linarith only [hdelta1, ht012c, hbg3c, hbg0a, ht134c, ht124b, hbg1b]
                          ·
                            linarith only [hdelta1, ht023b, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, ht134a, hbg3c, ht123c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 2 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc32, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h340, ht023a, ht123c, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h011, h130, ht023a, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h011, h230, ht023c, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, ht023a, ht134a, ht123c, ht034c, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, h011, h340, ht023a, hbg3c, hbg0a]
                        ·
                          linarith only [hdelta1, h011, h340, ht023c, hbg3c, ht123c, hbg0a]
                        ·
                          linarith only [hdelta1, ht023a, hbg3c, ht123c, ht034c, hbg0c]
                        ·
                          linarith only [hdelta1, h011, h120, ht023c, hbg3c, ht134c, ht124b, hbg0a]
                        ·
                          linarith only [hdelta1, ht023b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht134a, hbg3c, ht123c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht124c, ht123b, ht134b]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht123c, ht234a, ht134a]
                    ·
                      have hb1 := m.budget 1 (by decide) 4 2 3 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h011, h140, ht012c, ht023a, ht123a, hbg1]
                      ·
                        linarith only [hdelta1, h011, h340, ht013a, ht234b, ht124a, hbg1]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 2 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc32, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hn, hdelta1, h011, h340, hbg3, hbg1]
                        ·
                          linarith only [hdelta1, ht012d, ht023a, ht123b, hbg3]
                        ·
                          linarith only [hdelta1, h011, h340, ht012c, ht123a, ht023c, ht234b, hbg3, ht124a]
                        ·
                          linarith only [hdelta1, ht023b, ht123a, ht234b, hbg3, ht124a]
                        ·
                          linarith only [hdelta1, h011, h340, hbg1, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h340, hbg1, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h340, hbg1, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h240, ht012c, ht123b, ht023c, ht124a, hbg3c]
                        ·
                          linarith only [hdelta1, ht023b, ht123b, ht234b, ht124a, hbg3c]
                        ·
                          linarith only [hdelta1, ht123a, ht234b, ht124a, hbg3c]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, ht124c, ht123a, hbg1]
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht023a, hbg1c, ht123c, ht234b, ht124b]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 2 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc32, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h140, h340, ht012c, ht023a, ht123a, hbg1c, hbg3]
                        ·
                          linarith only [hdelta1, h011, h340, ht012c, ht023a, ht123b, ht234b, ht124b, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, h011, h340, ht012c, ht123a, ht023c, ht234b, ht124b, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, ht013b, ht123b, ht234b, ht124b, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, h011, h340, ht012c, ht023a, hbg3c]
                        ·
                          linarith only [hdelta1, h011, h340, ht012c, ht123a, ht023c, hbg1c, hbg3c, ht234b, ht124b]
                        ·
                          linarith only [hdelta1, h011, h340, ht023b, ht123a, hbg1c, hbg3c, ht234b, ht124b]
                        ·
                          linarith only [hdelta1, h011, h340, ht012c, ht123b, ht023c, hbg3c, ht234b, ht124b, hbg1a]
                        ·
                          linarith only [hdelta1, ht023b, ht123b, hbg3c, ht234b, ht124b, hbg1a]
                        ·
                          linarith only [hdelta1, ht123a, hbg3c, ht234b, ht124b, hbg1a]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, ht123a, hbg1c]
                      ·
                        linarith only [hdelta1, h011, h340, ht234b, ht124a, hbg1c]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, ht124c, ht123c, hbg1c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 2 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc32, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h340, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, ht012c, ht023a, ht124c, ht123b, hbg1b, hbg3]
                        ·
                          linarith only [hdelta1, ht012c, ht124c, ht123a, ht023c, hbg1b, hbg3]
                        ·
                          linarith only [hdelta1, ht023b, ht123a, ht234b, ht124a, hbg3]
                        ·
                          linarith only [hdelta1, h021, h340, ht023a, hbg3c]
                        ·
                          linarith only [hdelta1, h011, h340, ht012c, ht124c, ht123a, hbg3c, ht023c, hbg1c]
                        ·
                          linarith only [hdelta1, ht023b, ht124c, ht123a, hbg3c, hbg1c]
                        ·
                          linarith only [hdelta1, h011, h240, ht012c, hbg3c, ht123b, ht023c, ht124a]
                        ·
                          linarith only [hdelta1, ht023b, hbg3c, ht123b, ht234b, ht124a]
                        ·
                          linarith only [hdelta1, ht123a, hbg3c, ht234b, ht124a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 1 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc31, hc30] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht024a, hbg3, ht124a, ht123c]
                      ·
                        linarith only [hdelta1, ht013d, ht034a, hbg3]
                      ·
                        linarith only [hdelta1, ht012d, ht023c, hbg3, ht234c, ht124a]
                      ·
                        linarith only [hdelta1, ht123a, ht034a, hbg3, ht234c, ht124a]
                      ·
                        linarith only [hdelta1, ht034a, ht023d, hbg3c]
                      ·
                        linarith only [hdelta1, ht023d, ht234c, ht124a, ht123c, hbg3c]
                      ·
                        linarith only [hdelta1, ht024b, ht124a, ht123c, ht034c, hbg3c]
                      ·
                        linarith only [hdelta1, ht013d, hbg3c]
                      ·
                        linarith only [hdelta1, ht123b, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht123a, ht234c, ht124a, hbg3c]
                    ·
                      linarith only [ht123b, ht134a, ht234a]
                  ·
                    linarith only [ht124b, ht123c, ht134c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 1 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc31, hc30] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht034a, ht023d, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht013d, ht034a, hbg3]
                      ·
                        linarith only [hdelta1, ht123b, ht023d, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht123b, ht034a, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, hbg3c, ht034a, ht023d]
                      ·
                        linarith only [hdelta1, hbg3c, ht023d, ht134a]
                      ·
                        linarith only [hdelta1, hbg3c, ht034a, ht134a]
                      ·
                        linarith only [hdelta1, ht013d, hbg3c]
                      ·
                        linarith only [hdelta1, hbg3c, ht123b, ht034a]
                      ·
                        linarith only [hdelta1, hbg3c, ht123b, ht134a]
                    ·
                      linarith only [ht123b, ht134a, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 4 1 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc31, hc30] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, h011, h230, ht012a, hbg3, ht134a, ht123c]
                      ·
                        linarith only [hdelta1, h011, h230, ht012a, hbg3, ht123c, ht234a]
                      ·
                        linarith only [hdelta1, ht023d, hbg3, ht134a, ht234a]
                      ·
                        linarith only [hdelta1, ht013b, hbg3, ht134a, ht234a]
                      ·
                        linarith only [hdelta1, h011, h230, ht012a, hbg3c, ht123c]
                      ·
                        linarith only [hdelta1, ht023d, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013b, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023d, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht013b, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht134a, hbg3c, ht234a]
                    ·
                      have hb1 := m.budget 1 (by decide) 4 3 2 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        have hb3 := m.budget 3 (by decide) 4 2 1 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h340, ht012a, ht123a, hbg3]
                        ·
                          linarith only [hdelta1, h011, h340, ht012a, ht123c, ht234a, hbg3]
                        ·
                          linarith only [hn, hdelta1, h011, h340, ht012c, ht023c, ht124b, ht234b, hbg3, hbg1]
                        ·
                          linarith only [hn, hdelta1, ht013b, ht124b, ht234b, hbg3, hbg1]
                        ·
                          linarith only [hdelta1, h011, h340, ht012a, hbg3c, ht123c]
                        ·
                          linarith only [hdelta1, h011, h340, ht012c, ht023c, hbg3b, ht124b, ht234b, hbg1]
                        ·
                          linarith only [hdelta1, ht013b, hbg3b, ht124b, ht234b, hbg1]
                        ·
                          linarith only [hdelta1, h031, h340, hbg3b, ht124b, ht234b, hbg1]
                        ·
                          linarith only [hdelta1, ht013b, hbg3b, ht124b, ht234b, hbg1]
                        ·
                          linarith only [hdelta1, h031, h340, hbg3a, ht124b, ht234b, hbg1]
                      ·
                        linarith only [hdelta1, h011, h340, ht012a, ht134a, hbg1]
                      ·
                        linarith only [hdelta1, h011, h340, ht123a, ht234a, hbg1]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 2 1 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h340, ht012a, ht123a, hbg3]
                        ·
                          linarith only [hdelta1, h011, h340, ht013a, hbg3, ht234a]
                        ·
                          linarith only [hn, hdelta1, ht012c, ht023c, ht134c, hbg3, hbg1]
                        ·
                          linarith only [hdelta1, ht012a, ht013b, ht123a, ht134c, hbg3, ht234a, hbg1]
                        ·
                          linarith only [hdelta1, h011, h340, ht012a, hbg3c, ht123c]
                        ·
                          linarith only [hdelta1, ht012c, ht023c, ht134c, hbg3b, hbg1]
                        ·
                          linarith only [hdelta1, ht012a, ht013b, ht123a, ht134c, hbg1, hbg3c]
                        ·
                          linarith only [hdelta1, ht012c, ht023c, ht134c, hbg3b, hbg1]
                        ·
                          linarith only [hdelta1, ht013b, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, ht012c, ht023c, ht134c, hbg3a, hbg1]
                      ·
                        linarith only [hdelta1, h011, h140, ht012a, hbg1c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 2 1 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h340, ht123a, hbg3, hbg1b]
                        ·
                          linarith only [hdelta1, h011, h230, hbg3, ht123c, hbg1b]
                        ·
                          linarith only [hdelta1, h011, h340, ht012c, hbg1a, ht023c, ht124b, hbg3, ht234b]
                        ·
                          linarith only [hdelta1, ht013b, hbg1a, ht124b, hbg3, ht234b]
                        ·
                          linarith only [hdelta1, h011, h340, hbg3c, ht123c, hbg1b]
                        ·
                          linarith only [hdelta1, h011, h140, h340, ht012c, ht123a, ht023c, hbg3c, hbg1c]
                        ·
                          linarith only [hdelta1, h011, h340, ht013b, ht123a, ht124b, hbg3c, ht234b, hbg1c]
                        ·
                          linarith only [hdelta1, ht023d, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, hbg3c, ht234a]
                        ·
                          linarith only [hdelta1, h011, h340, ht123a, ht124b, hbg3c, ht234b, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht123c, hbg1c]
                      ·
                        linarith only [hdelta1, h011, h340, ht123b, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht134c, hbg1c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 2 1 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h340, ht123a, hbg3, hbg1a]
                        ·
                          linarith only [hdelta1, h011, h230, hbg3, ht123c, hbg1a]
                        ·
                          linarith only [hdelta1, ht012c, ht023c, hbg1b, ht134c, hbg3]
                        ·
                          linarith only [hdelta1, ht013b, ht123a, ht134c, hbg3, ht234a, hbg1c]
                        ·
                          linarith only [hdelta1, h011, h340, ht013a, hbg3c]
                        ·
                          linarith only [hdelta1, h011, h340, ht012c, ht123a, ht023c, ht134c, hbg1c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht123a, ht134c, hbg1c, hbg3c]
                        ·
                          linarith only [hdelta1, ht023d, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, ht123b, ht234a, hbg3c]

#print axioms model_impossible_2
end Jsp404.GlobalFiveLowTerminal
