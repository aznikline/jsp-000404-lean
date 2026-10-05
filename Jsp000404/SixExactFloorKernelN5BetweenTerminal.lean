import Jsp000404.SixExactFloorKernelN5BetweenM000
import Jsp000404.SixExactFloorKernelN5BetweenM001
import Jsp000404.SixExactFloorKernelN5BetweenM003
import Jsp000404.SixExactFloorKernelN5BetweenM007
import Jsp000404.SixExactFloorKernelN5BetweenM011
import Jsp000404.SixExactFloorKernelN5BetweenM015
import Jsp000404.SixExactFloorKernelN5BetweenM031
import Jsp000404.SixExactFloorKernelN5BetweenM063
import Jsp000404.SixExactFloorKernelN5BetweenM064
import Jsp000404.SixExactFloorKernelN5BetweenM072
import Jsp000404.SixExactFloorKernelN5BetweenM074
import Jsp000404.SixExactFloorKernelN5BetweenM075
import Jsp000404.SixExactFloorKernelN5BetweenM079
import Jsp000404.SixExactFloorKernelN5BetweenM095
import Jsp000404.SixExactFloorKernelN5BetweenM127
import Jsp000404.SixExactFloorKernelN5BetweenM192
import Jsp000404.SixExactFloorKernelN5BetweenM200
import Jsp000404.SixExactFloorKernelN5BetweenM202
import Jsp000404.SixExactFloorKernelN5BetweenM216
import Jsp000404.SixExactFloorKernelN5BetweenM218
import Jsp000404.SixExactFloorKernelN5BetweenM222
import Jsp000404.SixExactFloorKernelN5BetweenM223
import Jsp000404.SixExactFloorKernelN5BetweenM254
import Jsp000404.SixExactFloorKernelN5BetweenM255
import Jsp000404.SixExactFloorKernelN5BetweenM448
import Jsp000404.SixExactFloorKernelN5BetweenM456
import Jsp000404.SixExactFloorKernelN5BetweenM472
import Jsp000404.SixExactFloorKernelN5BetweenM504
import Jsp000404.SixExactFloorKernelN5BetweenM508
import Jsp000404.SixExactFloorKernelN5BetweenM510
import Jsp000404.SixExactFloorKernelN5BetweenM511
import Jsp000404.SixExactFloorKernelN5BetweenM512
import Jsp000404.SixExactFloorKernelN5BetweenM513
import Jsp000404.SixExactFloorKernelN5BetweenM515
import Jsp000404.SixExactFloorKernelN5BetweenM519
import Jsp000404.SixExactFloorKernelN5BetweenM551
import Jsp000404.SixExactFloorKernelN5BetweenM567
import Jsp000404.SixExactFloorKernelN5BetweenM575
import Jsp000404.SixExactFloorKernelN5BetweenM768
import Jsp000404.SixExactFloorKernelN5BetweenM769
import Jsp000404.SixExactFloorKernelN5BetweenM800
import Jsp000404.SixExactFloorKernelN5BetweenM801
import Jsp000404.SixExactFloorKernelN5BetweenM805
import Jsp000404.SixExactFloorKernelN5BetweenM807
import Jsp000404.SixExactFloorKernelN5BetweenM821
import Jsp000404.SixExactFloorKernelN5BetweenM823
import Jsp000404.SixExactFloorKernelN5BetweenM831
import Jsp000404.SixExactFloorKernelN5BetweenM896
import Jsp000404.SixExactFloorKernelN5BetweenM928
import Jsp000404.SixExactFloorKernelN5BetweenM944
import Jsp000404.SixExactFloorKernelN5BetweenM948
import Jsp000404.SixExactFloorKernelN5BetweenM949
import Jsp000404.SixExactFloorKernelN5BetweenM951
import Jsp000404.SixExactFloorKernelN5BetweenM959
import Jsp000404.SixExactFloorKernelN5BetweenM960
import Jsp000404.SixExactFloorKernelN5BetweenM992
import Jsp000404.SixExactFloorKernelN5BetweenM1008
import Jsp000404.SixExactFloorKernelN5BetweenM1012
import Jsp000404.SixExactFloorKernelN5BetweenM1016
import Jsp000404.SixExactFloorKernelN5BetweenM1020
import Jsp000404.SixExactFloorKernelN5BetweenM1022
import Jsp000404.SixExactFloorKernelN5BetweenM1023

/-! Complete ten-triangle disjunction coverage. No acyclic-orientation hypothesis. -/
namespace Jsp404.SixExactFloorKernel

set_option maxHeartbeats 16000000 in
theorem n5_between_impossible (M : SixModelCompression.ModelSix 5)
    (hhigh : (1/2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    : False := by
  rcases M.triangle 0 1 2 (by decide) (by decide) with htri012 | htri012
  ·
    have htr012a := htri012.1
    have htr012b := htri012.2.1
    have htr012c := htri012.2.2
    rcases M.triangle 0 1 3 (by decide) (by decide) with htri013 | htri013
    ·
      have htr013a := htri013.1
      have htr013b := htri013.2.1
      have htr013c := htri013.2.2
      rcases M.triangle 0 1 4 (by decide) (by decide) with htri014 | htri014
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask000 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask512 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr123c, htr134a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask768 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134b, htr123b, htr124c]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134b, htr123a, htr124c, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask896 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask064 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr124b, htr234a, htr134c, htr123a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr124b, htr123c, htr134c]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask192 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr123b, htr234a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask448 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask960 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask800 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr134a, htr034a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask928 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr123c, htr134c, htr124b]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask992 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr023b, htr034b, htr024c]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012c, htr124a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask944 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr023a, htr024a, htr124a, htr123a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask1008 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask072 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013c, htr023b, htr134a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134c, htr123c, htr124b]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask200 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023a, htr024a, htr134c, htr124b, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask456 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023a, htr024b, htr234a, htr034c]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr024b, htr034c, htr023c]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr124a, htr012c]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask216 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013c, htr023b, htr234a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask472 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr034a, htr234a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012c, htr124a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013c, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask504 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask1016 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr012b, htr014c, htr024b]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr023b, htr012b, htr014c, htr034b]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012c, htr124a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134b, htr014a, htr012a, htr234a, htr123a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask948 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr023a, htr123a, htr124a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr134a, htr034a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr014a, htr023a, htr012b, htr234a, htr134b]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask1012 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr013b, htr023c, htr024b, htr014c]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr013b, htr014c, htr034b]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr123a, htr012c, htr023a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012c, htr124a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013c, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask508 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask1020 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
    ·
      have htr013a := htri013.1
      have htr013b := htri013.2.1
      have htr013c := htri013.2.2
      rcases M.triangle 0 1 4 (by decide) (by decide) with htri014 | htri014
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          linarith only [htr023b, htr013c, htr012b]
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask074 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr234a, htr013a, htr012a, htr123b, htr134c, htr124b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask202 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr024a, htr013a, htr012b, htr234a, htr134c, htr123b, htr124b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr034c, htr013c, htr012b, htr024b]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr012c, htr024a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask218 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr014a, htr013a, htr123b, htr234a, htr134c]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr014b, htr034c, htr013c]
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          linarith only [htr013c, htr012b, htr023b]
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr014c, htr012b, htr024b]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012c, htr023a, htr123a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr024a, htr012c]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask222 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr034a, htr013b, htr234a, htr123b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr123a, htr012c, htr023a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr024a, htr012c]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask254 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134a, htr234a, htr123b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask510 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask1022 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
  ·
    have htr012a := htri012.1
    have htr012b := htri012.2.1
    have htr012c := htri012.2.2
    rcases M.triangle 0 1 3 (by decide) (by decide) with htri013 | htri013
    ·
      have htr013a := htri013.1
      have htr013b := htri013.2.1
      have htr013c := htri013.2.2
      rcases M.triangle 0 1 4 (by decide) (by decide) with htri014 | htri014
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask001 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask513 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr234a, htr123c, htr134a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask769 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012b, htr124a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012b, htr123a, htr023a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr134a, htr034a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013c, htr123c, htr234a, htr034a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask801 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr024a, htr012b]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012b, htr023a, htr123a]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr012c, htr014b, htr024c]
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          linarith only [htr012c, htr013b, htr023c]
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr013b, htr034b, htr014c]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr014a, htr013a, htr134b, htr123c, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask805 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012b, htr124a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012b, htr123a]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr012c, htr013b, htr024c, htr034b]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr012c, htr234a, htr013a, htr024a, htr124c, htr123c, htr134b]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask821 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013a, htr134b, htr012a, htr123c, htr234a, htr124c]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask949 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr123a, htr012b]
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          linarith only [htr012c, htr023c, htr013b]
    ·
      have htr013a := htri013.1
      have htr013b := htri013.2.1
      have htr013c := htri013.2.2
      rcases M.triangle 0 1 4 (by decide) (by decide) with htri014 | htri014
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask003 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask515 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012b, htr124a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012b, htr123a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr014b, htr034c, htr013c]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr014b, htr024c, htr023b, htr013c]
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask011 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr012c, htr134c, htr014a, htr023a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr134a, htr034a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr123a, htr023a, htr024a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask075 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134c, htr123a, htr012a, htr014a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr134a, htr034a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr012b, htr124a, htr024a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr012c, htr023c, htr034c, htr014b]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr012c, htr014b, htr024c]
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask007 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask519 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr134a, htr034a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr012b, htr124a, htr024a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012b, htr023a, htr123a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask551 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013b, htr023c, htr134a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask807 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr012b, htr024a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr123a, htr012b, htr023a]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr034b, htr024c, htr023b]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr034b, htr234a, htr023a, htr024c]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask567 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr024a, htr234a, htr023a, htr134b, htr124c]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask823 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134b, htr124c, htr123b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013b, htr234a, htr023c, htr134a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask951 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012b, htr123a, htr023a]
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask015 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr034a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr123a, htr023a, htr024a, htr124a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask079 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr034a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr012b, htr024a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr023c, htr024b, htr034c]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask031 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr234a, htr023b, htr034a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr124c, htr123b, htr134b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask095 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr234a, htr034a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134a, htr013b, htr034a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask223 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr034a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask063 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask575 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr123c, htr234a, htr134a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask831 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr123b, htr134b, htr124c]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr123a, htr234a, htr134b, htr124c]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask959 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask127 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134c, htr124b, htr123a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134c, htr123c, htr124b]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask255 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134a, htr234a, htr123b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask511 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact n5_between_mask1023 M hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234

#print axioms n5_between_impossible
end Jsp404.SixExactFloorKernel
