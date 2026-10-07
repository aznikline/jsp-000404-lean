import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard040
open N4R2OuterLeftReplay

-- Cycle fingerprint 009457d484a6bde8001058c00ccbab820d10bf394f4074d84af593450c0d7bba.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint 072dd358944bbf56ba9ecd239e4be3734ac8fd873eea3987737092153b247a75.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .triangle 28 1, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 09de3b4e093e4b4265fbc1fc29808234d2bf61c805ed8d0c2f257616c387830e.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 2 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 0bb126421cf7813b4816813770296f382c126c2b708f2f6487917997daa44309.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 0c41b1c874788fe21a68e186c5734c18c5decc9222e3a0a9ab6a8a669d1e277c.
def localCycle00004 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 5]

-- Cycle fingerprint 0f1a91db3189124ee0282b1f522738201c715df41fbbf6e7b595a75df9fd3e74.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 28 1, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0fd603a830013211d927c46950c4957b1e806ab1b5e0873ede898309a0a71c5b.
def localCycle00006 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 11cc4ff3cbf0d9d5dc7ae27ae36b0332a34e3d3b97a8b85fe34e280455f0c18c.
def localCycle00007 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 142f6625b360c29a6b0a0479afa7ab31d849a38c288722bd63ad847f4e8e8d21.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 15cdcce8494aa68c5f2f3b715eff6255c547c256cacd0534f3f504f6e1699487.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 1ffed21dfa63b880b28c591f05c3ab9fd004e7375ba2e7d4bfcd0aecbdb2a97b.
def localCycle00010 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 211e30826b9e64abb7219926b1ece7b1ad446f6671a3e5311cb87450749ab8c2.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 24257ad5965ff745bb0c18cb9daf3311b868c7ea6ee6e9d0e021e7b2d90ab110.
def localCycle00012 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 25612142e553fb22d19ca0434b4503084f5c3439d6b6ae4ac2e2d9e84e91b74b.
def localCycle00013 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 26a99f8a6a37a8fdb008f50baf70bf15436967e34c900e7027af6e36286bfe97.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2bf437a2c9892a866a793f6281aaf07a26553b4553d4984b03b47d23fce1bd96.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 25 2, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 3009e6d9c4b5afe74b060e5fd4ac3926ead7dda54f3b3662410ae7729629e64f.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 29 2, .triangle 8 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 3295a7a09004ae0284bf2f3e7ba9d09d65bed005921b2ca197a066994e7d1085.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 372e03f850b3b57db06c97fa3adc87af1855c624f26cef91d76cc91a74e783f4.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 2, .triangle 8 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 38834be2c33d89fb018de3aacbac69cd262e94723e49bfb65e67fb6f1cb56df9.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 3d9a5ffaec23ad0ded1e15597e1a1f4ed4288dae22fb3c42abc6731021140c61.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 4c036d30d3cc33d7dabd6d4cb4460089edbbedf1c9cb3f21bbe1dfa612c3a714.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 4f73d829b088fdf4a988bcd40b3a8c6f06f3cb65432f46276355e14fb2a8dbe5.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 52f32d4effdbe50f04e09dd3126ac31e809c1c43449d40e36deeca619220ab98.
def localCycle00023 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 53779025bd0ee137ef8bb333f4bdfb0d54229e3cf6e93795b76624cf7a4daf5b.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 55a37dbba275dd4dc7134675ed01e893e81004dbe02f4b64066991336f85f5bd.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint 5689f97dd2f46f791eb0d307dea100534cc1c50eddf034171900b9afd65816d9.
def localCycle00026 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 5abbf82859b6cd03bbd04c9b72fb0ce93fde7db39d49b4491c4702e52d6f5ec2.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 5aeadc848a49bd245cd172491618e7b5e8c4e28237f416332772c836260b9b37.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 29 2, .triangle 30 1, .triangle 7 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 5af6aeb3dee483f2366dd56927fab79416c80d8991b31bd6859ef3ec85088be8.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .gapLower 3 0]

-- Cycle fingerprint 5b646f9766c7cc288eaa0b5011bf153246a18ea22f3e33f02f63fa12b45e3129.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 5de915ea574578b33aa4d53b4ecd6673c433736e77f2c90235b44a28c7327d1b.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 5f1534a8071e8f9d2a89df4b9c8bdcd606098ab64305d9688ce22441d9cfa0dd.
def localCycle00032 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 605d71e2cd0dd8b75ffd899fb67281ded0bca34e769823cf977c2b9c1f60df45.
def localCycle00033 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 60f8f35477e039f0bda01d60fa8c9c1374d639eb2e5cdab8d7bba48950abdf0c.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 610400477948cd0df6b530b5245d79d77a20bc8a3b193d882b5268802e5833b7.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 6127bf8e17c7aff901126dd5f487416b0f8735eb20d782f1584b82709f33347a.
def localCycle00036 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 612fae958a215195afb16555097148b93e9e59a4c89da1502eccbb874ac2aea0.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 64b268e29eebdeb49e706f0609508b93f92cfb59d10c08c035f252c10d4ebebb.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 28 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 65f269e5db87f9bc513119d066e6780f1c1f8c74288f46a658250cc946cbf135.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 6b69605fabcc246ae163b155be83c221f15267128605c461bb15cf223ccca896.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 6c410f79f6c55674692efc5b12a9c680858d4af03980ea192ca33e6cf3e45131.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 29 1, .corridorLower 4 6]

-- Cycle fingerprint 6e781f653edb6bb1d3c9f61c6ace511d5eddb42cf180f26b7574ed47a02ed6dd.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 70276417b542aa27cd14e5063cdd940d046f8bcb97852e0892871da18be75df8.
def localCycle00043 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 740314f049c09d8810582468eb4358749f70a59e50d4e5cbe9ae7715ea01cf8a.
def localCycle00044 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 7453941c10f69214e25b77a30ee5c4294c2e63c61e1594b119d1082dd6573449.
def localCycle00045 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 75fc13e3d6fe347a481317c8487a517b4975bfd988ce90c9460dc694b549027b.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 76b0afc27ae47420bc05b484a79322647391c96986d58e843c0d73db6bd5a575.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 770dff0a06c512b84ea08af76fa3629d5079bd38faf1015e8b0daa78aaf6fbc4.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint 77b325e443b44d1282607b9da95932dd9aca28640f38236fb261fb0427aefe52.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 791ac4b8889e9ac4293c10dfc07c3d2b178e61325fecd3e1500b57748c720789.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .gapLower 3 0]

-- Cycle fingerprint 7dc32452f43fc52627a4373f33d16605c821993928382923f61070aaefed1527.
def localCycle00051 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 7eb3bb515aade1773e6b432409db748e1f7a108626b609c5bbd0576330307dfa.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 7f82ca7306353ecbdf6ec49ff69d3f4724f898606969ee53805c6548315ec1e1.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 80e108502767fe648ad96b41536994bd33d807f8b6454ed5606afacc3c6db55d.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 81a7939f72302e06d22dbfbcf7f386931a6942ad062b6df94120a574584b2fd2.
def localCycle00055 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 86a0bb70a75ec4d234ed0b1573cb72feeca3ccc6378d31a16e095ff5c242b240.
def localCycle00056 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 89e2bb2ab40ae7f788ae1f3f7762ee46a28d29abe9ab02e961983a05059f8f87.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 8a1c2922db13d3d0c7ad3679a0adc99213537774eb5edeea8447fe5eb4872241.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 28 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 8b9618177055b8e7b0dc27ffe41c26b0b454ca76c32652fe3fbd5eb7df3519d4.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 93c9547ddb9c974ced299c6c58a7cdf375ff8fbe675727cb31f7e964bcac006e.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 93ec46c899a8fb42798b925e4839308afb17a0e1d155f5e10de511f789cb41c5.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 95619e5061c7284586fa0faf03178bccdcacb4f5263c5dc905c8d0e5d455fc6e.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 9578af5b5eebedc990c0c2e768622f313c51266bddb5f6a7c58ab85c93c2a20c.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 9757b1017a7a46ce997514072ca63a8196ee6f411680ff1c27ac697dc6cfde29.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 9778c9a8042ecd3f93e01ee5bddb265fae9dfe9291d180b103687d5d4115603a.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 97db9f4f6cf48f1d2a50b284ea47920fa4792741523f069f23f355fa865b2426.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 9a9a4cfba08477a1832873ec10af868c6b81b76783148fd7cb14f1749f5c8bf0.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint 9fafd707fcea78552b4ca004ebefb20466f587fe31dd0ca2db7cc03cf4e6b54c.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint a0da871f74b2bdf44a734e250eafe6e1f7f63ec0bd96c9be3dda18ada48b9616.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint a3230d6505e689232e89a450a0d5038f79def2d214fb6053ee38a3d554302c86.
def localCycle00070 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint a67c42f5731eaf00f572622a0f942dc136a63c6691bb1a45d6dd70203ab79105.
def localCycle00071 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .triangle 25 2, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint a8a2da70aea10d630e69886cdc9aeeff40c1bece307f414a7c731d3b807c1fa6.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint a97a52d4f2e49365945d98967ff62c0b2b02153ed310428dae0f1dda132a5add.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 3, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint aa16e4a6974d4d40d8480788324e64f10c39e1810b68e3df45620f2e9dff1d66.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0, .gapLower 3 0]

-- Cycle fingerprint abb62912f975bc06ebeb923c8a52f34e46510a10f512fc992a2647ffdf0dc50d.
def localCycle00075 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint bb2df25d6334417fe871e93394951fdb9c39c932f9ae255343268e6b135675a2.
def localCycle00076 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint c0981af014c371a71218aa23834fa5888cfa256f9e7f2ee0bffa3c13b697a74b.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint c5a76cd10eaedddbda20727854a47f817453067bdbd1fd34e3884c356d36734d.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint c5edb94b522f0e2ef1af9d238ba7f5f3822a2b6931aa290b9d0238ad3e461655.
def localCycle00079 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d1ea220bc22f0e7df0b250c659912e4498289a7996b4835ad84153a60cd6fa43.
def localCycle00080 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint d5d4571b5f5f81fa4bf1a430ed55f7b72f7a9a220d4816f70e9619c0144aebb3.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d62b5a17a3fa3d1d938e3e1b182a465043fd11e9ada8192967851edafcd5d212.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true] }
  origin := ![.triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 5]

-- Cycle fingerprint d6a5110d8774884090a1f1056b84cc7145aac06c52406326309bd6ca98678a19.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint d838d4e00677744ea153fe741720aaf87a885ce2f17837704b19d80fca705532.
def localCycle00084 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint d98d3571c6d9fd04bb76cc318a6ff21d638cfde5dd642ec53e4f4c7967b7a727.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint d9d311f4964afe3dad4f875998e02897603a7315aa8d5d3e7ee2dae9304b6b6c.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint db7e89df2de8b84fed3d9bc169672af6870691a17a6bdc0f80d1bd9de4ed34db.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint e2f341ea330dcd43e75a8cf6afc45c8fc3645176a92b0599e605ed1a623a81e6.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 26 1, .gapLower 3 0]

-- Cycle fingerprint e509efde5ae14ca6289e562a511c5d2ce73928e0d32df0d7b884c28963287f50.
def localCycle00089 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint ea6c869b0b64f2de2e56f135e10655de68c172bf3bc828cff2096519ec20f849.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint eb0733ef2340780e04584639d254444d8989bb7c2402b55ae66c85d11c45d533.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint edef58775c41a3993268e825104de6a0f1c6c21b941c959b92b27d5ff3837205.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 26 1, .gapLower 3 0]

-- Cycle fingerprint ef43278f28c4030702f667ac5bf0ca812b1fcde47a3525dead3467a0535d8102.
def localCycle00093 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint f2706841287d06f2f8a8629870baae07113c20e026e52ca6518e960291db7881.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint f2926c4a73d5ae2ff4bb8990e9d9d4e24f9823593ec1d33d54580ada0c395b64.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint f2da3d3ef175ec894fa5d4af9443b2e63fb3ae01fda25f5cf016f6db211bb0bf.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .gapLower 3 0]

-- Cycle fingerprint f5b3085286439fafb8f24e5cff5c0d07757bef5aec7f1a6cb841adfcc0527310.
def localCycle00097 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint f95ab7853f9402e990bcd47fd6bfad7c84fe35af42cc41d5964b7af2665b4a2a.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint fd1361ca47130a66e1f396b018b9dfcd670eca738d9e292a50217a303ee7cea6.
def localCycle00099 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint fd5bce5cf8136f37000dcb1167c67627faf6c1b64b2a5a7f0e11658360062a86.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

def library : Library := fun id => if id < 50 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 37 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))) else (if id < 43 then (if id < 40 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)))) else (if id < 46 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))))))) else (if id < 75 then (if id < 62 then (if id < 56 then (if id < 53 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 59 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))))) else (if id < 68 then (if id < 65 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))))) else (if id < 88 then (if id < 81 then (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)))) else (if id < 84 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))))) else (if id < 94 then (if id < 91 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))) else (if id < 97 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 4, 3, 5, 2], ![3, 6, 0, 4, 5, 1], ![2, 6, 0, 4, 1, 5], ![6, 0, 2, 3, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 69 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5120)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 4, 3, 5, 2], ![6, 3, 0, 4, 5, 1], ![6, 2, 0, 4, 1, 5], ![6, 0, 2, 3, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 76 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5121)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 4, 5, 3, 2, 6], ![3, 0, 4, 5, 1, 6], ![2, 0, 4, 5, 1, 6], ![0, 2, 3, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 10 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5122)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 4, 5, 3, 2, 6], ![3, 0, 4, 5, 1, 6], ![2, 0, 4, 5, 1, 6], ![0, 2, 3, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 43 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5123)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 4, 5, 3, 6, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 5, 1, 6], ![0, 2, 3, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 6 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5124)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 4, 5, 3, 6, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 5, 1, 6], ![0, 2, 3, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 43 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5125)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 4, 5, 6, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![0, 2, 3, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 15 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5126)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 4, 5, 6, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![0, 2, 3, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 5 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5127)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![0, 2, 3, 1, 6, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 1, 4]], proof := .tail 73 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5128)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 6, 5, 1], ![0, 2, 3, 1, 6, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 52 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5129)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![3, 0, 4, 6, 5, 1], ![2, 0, 4, 6, 5, 1], ![0, 2, 3, 1, 6, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 63 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5130)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![0, 2, 3, 6, 1, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 91 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5131)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 6, 5, 1], ![0, 2, 3, 6, 1, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 91 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5132)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 6, 4, 5, 1], ![0, 2, 6, 3, 1, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 4, 3, 1]], proof := .tail 87 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5133)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 0, 4, 6, 5, 1], ![2, 0, 4, 6, 5, 1], ![0, 2, 3, 6, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 91 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5134)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 0, 4, 6, 5, 1], ![2, 0, 6, 4, 5, 1], ![0, 2, 6, 3, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 4, 3, 1]], proof := .tail 87 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5135)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 0, 6, 4, 5, 1], ![2, 0, 6, 4, 5, 1], ![0, 6, 2, 3, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 4, 2, 3, 1]], proof := .tail 55 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5136)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 4, 6, 5, 3, 2], ![3, 0, 4, 6, 5, 1], ![2, 0, 4, 6, 5, 1], ![0, 2, 3, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 30 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5137)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 4, 5, 3, 2], ![3, 0, 4, 6, 5, 1], ![2, 0, 4, 6, 5, 1], ![0, 2, 3, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 91 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5138)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 4, 5, 3, 2], ![3, 0, 4, 6, 5, 1], ![2, 0, 6, 4, 5, 1], ![0, 2, 6, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 4, 3, 1]], proof := .tail 87 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5139)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 4, 5, 3, 2], ![3, 0, 6, 4, 5, 1], ![2, 0, 6, 4, 5, 1], ![0, 6, 2, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 4, 2, 3, 1]], proof := .tail 68 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5140)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 4, 5, 3, 2], ![3, 0, 6, 4, 5, 1], ![2, 0, 6, 4, 5, 1], ![6, 0, 2, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 4, 0, 2, 3, 1]], proof := .tail 16 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5141)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 6, 4, 5, 3, 2], ![3, 6, 0, 4, 5, 1], ![2, 0, 6, 4, 5, 1], ![6, 0, 2, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 4, 2, 0, 3, 1]], proof := .tail 86 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5142)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 4, 5, 3, 2], ![3, 6, 0, 4, 5, 1], ![2, 6, 0, 4, 5, 1], ![6, 0, 2, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 49 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5143)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 4, 5, 3, 2], ![6, 3, 0, 4, 5, 1], ![6, 2, 0, 4, 5, 1], ![6, 0, 2, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 80 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5144)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 4, 3, 2, 6], ![3, 0, 4, 5, 1, 6], ![2, 0, 4, 5, 1, 6], ![0, 2, 3, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 60 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5145)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 4, 3, 6, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 5, 1, 6], ![0, 2, 3, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 60 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5146)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![0, 2, 3, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 60 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5147)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![0, 2, 3, 5, 6, 1], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 20 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5148)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![0, 2, 3, 5, 6, 1], ![0, 2, 3, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 71 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5149)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![0, 2, 3, 6, 5, 1], ![0, 2, 3, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 1 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5150)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 4, 6, 5, 1], ![0, 2, 3, 6, 5, 1], ![0, 2, 6, 3, 4, 1], ![0, 2, 5, 3, 4, 1]], proof := .tail 89 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5151)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 6, 4, 5, 1], ![0, 2, 6, 3, 5, 1], ![0, 2, 6, 3, 4, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 82 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5152)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 6, 5, 1], ![2, 0, 4, 6, 5, 1], ![0, 2, 3, 6, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 2, 3, 4, 1]], proof := .tail 34 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5153)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 6, 5, 1], ![2, 0, 6, 4, 5, 1], ![0, 2, 6, 3, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 2, 4, 3, 1]], proof := .tail 99 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5154)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 4, 5, 1], ![2, 0, 6, 4, 5, 1], ![0, 6, 2, 3, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 4, 2, 3, 1]], proof := .tail 61 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5155)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 6, 5, 1], ![2, 0, 4, 6, 5, 1], ![0, 2, 3, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 2, 3, 4, 1]], proof := .tail 34 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5156)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 6, 5, 1], ![2, 0, 6, 4, 5, 1], ![0, 2, 6, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 2, 4, 3, 1]], proof := .tail 99 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5157)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 4, 5, 1], ![2, 0, 6, 4, 5, 1], ![0, 6, 2, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 4, 2, 3, 1]], proof := .tail 61 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5158)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 4, 5, 1], ![2, 0, 6, 4, 5, 1], ![6, 0, 2, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 18 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5159)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 6, 5, 4, 3, 2], ![3, 6, 0, 4, 5, 1], ![2, 0, 6, 4, 5, 1], ![6, 0, 2, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 41 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5160)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 5, 4, 3, 2], ![3, 6, 0, 4, 5, 1], ![2, 6, 0, 4, 5, 1], ![6, 0, 2, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 62 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5161)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 5, 4, 3, 2], ![6, 3, 0, 4, 5, 1], ![6, 2, 0, 4, 5, 1], ![6, 0, 2, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 42 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5162)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 4, 3, 2, 6], ![3, 0, 4, 5, 1, 6], ![2, 0, 5, 4, 1, 6], ![0, 2, 5, 3, 1, 6], ![0, 2, 4, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 7 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5163)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 4, 3, 6, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 5, 4, 1, 6], ![0, 2, 5, 3, 1, 6], ![0, 2, 4, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 7 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5164)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 5, 4, 6, 1], ![0, 2, 5, 3, 1, 6], ![0, 2, 4, 3, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 54 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5165)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 5, 4, 6, 1], ![0, 2, 5, 3, 6, 1], ![0, 2, 4, 3, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 53 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5166)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 5, 6, 4, 1], ![0, 2, 5, 6, 3, 1], ![0, 2, 4, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 38 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5167)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 5, 4, 6, 1], ![0, 2, 5, 3, 6, 1], ![0, 2, 4, 3, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 45 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5168)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 5, 6, 4, 1], ![0, 2, 5, 6, 3, 1], ![0, 2, 4, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 19 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5169)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 6, 5, 4, 1], ![0, 2, 5, 6, 3, 1], ![0, 2, 4, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 35 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5170)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 5, 6, 1], ![2, 0, 6, 5, 4, 1], ![0, 2, 6, 5, 3, 1], ![0, 2, 6, 4, 3, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 4 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5171)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 6, 5, 1], ![2, 0, 6, 5, 4, 1], ![0, 2, 6, 5, 3, 1], ![0, 6, 2, 4, 3, 1], ![0, 5, 2, 4, 3, 1]], proof := .tail 65 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5172)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 4, 5, 1], ![2, 0, 6, 5, 4, 1], ![0, 6, 2, 5, 3, 1], ![0, 6, 2, 4, 3, 1], ![0, 5, 4, 2, 3, 1]], proof := .tail 72 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5173)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 5, 4, 3, 2], ![3, 0, 4, 6, 5, 1], ![2, 0, 6, 5, 4, 1], ![0, 2, 6, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 0, 2, 4, 3, 1]], proof := .tail 65 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5174)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 4, 5, 1], ![2, 0, 6, 5, 4, 1], ![0, 6, 2, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 0, 4, 2, 3, 1]], proof := .tail 72 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5175)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 4, 5, 1], ![2, 0, 6, 5, 4, 1], ![6, 0, 2, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 0 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5176)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 6, 5, 4, 3, 2], ![3, 6, 0, 4, 5, 1], ![2, 0, 6, 5, 4, 1], ![6, 0, 2, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 93 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5177)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 5, 4, 3, 2], ![3, 6, 0, 4, 5, 1], ![2, 6, 0, 5, 4, 1], ![6, 0, 2, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 97 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5178)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 5, 4, 3, 2], ![6, 3, 0, 4, 5, 1], ![6, 2, 0, 5, 4, 1], ![6, 0, 2, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 31 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5179)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 4, 3, 2, 6], ![3, 0, 5, 4, 1, 6], ![2, 0, 5, 4, 1, 6], ![0, 5, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 75 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5180)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 4, 3, 6, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 5, 4, 1, 6], ![0, 5, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 75 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5181)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 5, 4, 6, 1], ![0, 5, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 58 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5182)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 5, 4, 6, 1], ![0, 5, 2, 3, 6, 1], ![0, 4, 2, 3, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 83 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5183)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 5, 6, 4, 1], ![0, 5, 2, 6, 3, 1], ![0, 4, 2, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 67 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5184)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![3, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 95 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5185)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 5, 4, 6, 1], ![0, 5, 2, 3, 6, 1], ![0, 4, 2, 3, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 51 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5186)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 5, 6, 4, 1], ![0, 5, 2, 6, 3, 1], ![0, 4, 2, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 67 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5187)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 6, 5, 4, 1], ![0, 5, 2, 6, 3, 1], ![0, 4, 2, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 46 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5188)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 2, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 3 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5189)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 5, 6, 4, 1], ![2, 0, 6, 5, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 2, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 66 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5190)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 6, 2, 3, 1], ![0, 4, 5, 2, 3, 1]], proof := .tail 23 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5191)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 4, 1], ![0, 6, 5, 2, 3, 1], ![0, 6, 4, 2, 3, 1], ![0, 5, 4, 2, 3, 1]], proof := .tail 70 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5192)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 4, 1], ![0, 6, 5, 2, 3, 1], ![6, 0, 4, 2, 3, 1], ![5, 0, 4, 2, 3, 1]], proof := .tail 94 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5193)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 4, 1], ![6, 0, 5, 2, 3, 1], ![6, 0, 4, 2, 3, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 25 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5194)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 6, 5, 4, 3, 2], ![3, 6, 0, 5, 4, 1], ![2, 0, 6, 5, 4, 1], ![6, 0, 5, 2, 3, 1], ![6, 0, 4, 2, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 25 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5195)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 5, 4, 3, 2], ![3, 6, 0, 5, 4, 1], ![2, 6, 0, 5, 4, 1], ![6, 0, 5, 2, 3, 1], ![6, 0, 4, 2, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 13 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5196)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 5, 4, 3, 2], ![6, 3, 0, 5, 4, 1], ![6, 2, 0, 5, 4, 1], ![6, 0, 5, 2, 3, 1], ![6, 0, 4, 2, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 37 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5197)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 4, 3, 2, 6], ![3, 0, 5, 4, 1, 6], ![2, 0, 5, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 56 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5198)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 4, 3, 6, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 5, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 84 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5199)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 4, 6, 3, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 5, 4, 6, 1], ![5, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 27 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5200)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 5, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 11 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5201)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 5, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 0, 2, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 50 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5202)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 5, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 3 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5203)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 5, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 0, 2, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 67 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5204)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 5, 4, 6, 1], ![2, 0, 6, 5, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 0, 2, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 74 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5205)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![3, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 100 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5206)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 2, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 3 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5207)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 5, 6, 4, 1], ![2, 0, 6, 5, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 2, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 96 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5208)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 6, 2, 3, 1], ![0, 4, 5, 2, 3, 1]], proof := .tail 32 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5209)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 5, 6, 4, 3, 2], ![3, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 28 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5210)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![3, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 3 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5211)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![3, 0, 5, 6, 4, 1], ![2, 0, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 2, 6, 3, 1], ![4, 0, 2, 5, 3, 1]], proof := .tail 85 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5212)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 2, 3, 1]], proof := .tail 78 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5213)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 2, 3, 1]], proof := .tail 17 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5214)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![3, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 94 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5215)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 5, 4, 3, 2], ![3, 6, 0, 5, 4, 1], ![2, 0, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 0, 2, 3, 1], ![4, 5, 2, 0, 3, 1]], proof := .tail 81 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5216)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 5, 4, 3, 2], ![3, 6, 0, 5, 4, 1], ![2, 6, 0, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 0, 2, 3, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 48 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5217)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 5, 4, 3, 2], ![6, 3, 0, 5, 4, 1], ![6, 2, 0, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 0, 2, 3, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 8 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5218)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 5, 4, 3, 2], ![3, 6, 0, 5, 4, 1], ![2, 0, 6, 5, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 0, 2, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 21 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5219)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 5, 4, 3, 2], ![3, 6, 0, 5, 4, 1], ![2, 6, 0, 5, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 0, 2, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 64 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5220)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 5, 4, 3, 2], ![6, 3, 0, 5, 4, 1], ![6, 2, 0, 5, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 0, 2, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 12 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5221)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 4, 3, 2, 6], ![3, 5, 0, 4, 1, 6], ![2, 0, 5, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 2, 0, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 44 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5222)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 4, 3, 6, 2], ![3, 5, 0, 4, 6, 1], ![2, 0, 5, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 2, 0, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 44 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5223)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 4, 6, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 0, 5, 4, 6, 1], ![5, 0, 2, 3, 1, 6], ![4, 2, 0, 3, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 2 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5224)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 6, 4, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 0, 5, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 2, 0, 3, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 88 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5225)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 6, 4, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 0, 5, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 2, 0, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 77 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5226)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 0, 5, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 2, 0, 3, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 92 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5227)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 0, 5, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 2, 0, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 77 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5228)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 0, 6, 5, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 2, 0, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 22 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5229)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 6, 4, 3, 2], ![3, 5, 0, 6, 4, 1], ![2, 0, 5, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 2, 0, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 24 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5230)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 5, 0, 6, 4, 1], ![2, 0, 5, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 2, 0, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 24 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5231)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 5, 0, 6, 4, 1], ![2, 0, 6, 5, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 2, 0, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 79 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5232)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 5, 6, 4, 3, 2], ![3, 5, 0, 6, 4, 1], ![2, 0, 5, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 0, 3, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 57 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5233)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 6, 5, 4, 3, 2], ![3, 5, 0, 6, 4, 1], ![2, 0, 5, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 0, 3, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 14 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5234)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 6, 5, 4, 3, 2], ![3, 5, 0, 6, 4, 1], ![2, 0, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 0, 6, 3, 1], ![4, 0, 2, 5, 3, 1]], proof := .tail 47 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5235)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 5, 6, 4, 3, 2], ![3, 5, 6, 0, 4, 1], ![2, 0, 5, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 0, 3, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .tail 39 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5236)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 0, 4, 1], ![2, 0, 5, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 0, 3, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 39 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5237)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 0, 4, 1], ![2, 0, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 0, 6, 3, 1], ![4, 2, 0, 5, 3, 1]], proof := .tail 33 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5238)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 0, 4, 1], ![2, 0, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 6, 0, 3, 1], ![4, 2, 5, 0, 3, 1]], proof := .tail 29 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5239)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 0, 4, 1], ![2, 0, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 2, 0, 3, 1], ![4, 5, 2, 0, 3, 1]], proof := .tail 40 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5240)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 0, 4, 1], ![2, 0, 6, 5, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 2, 0, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 9 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5241)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 0, 4, 1], ![2, 6, 0, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 6, 0, 3, 1], ![4, 2, 5, 3, 0, 1]], proof := .tail 90 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5242)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 0, 4, 1], ![2, 6, 0, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 2, 0, 3, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 90 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5243)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 0, 4, 1], ![2, 6, 0, 5, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 2, 0, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 98 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5244)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 0, 4, 1], ![6, 2, 0, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 2, 0, 3, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 26 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5245)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 0, 4, 1], ![6, 2, 0, 5, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 2, 0, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 59 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5246)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 4, 3, 2, 6], ![3, 5, 0, 4, 1, 6], ![2, 5, 0, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 2, 3, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 36 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5247)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (5120 + j.val))) (lookup j.val) = true := by
  have hjbound : j.val < 128 := j.isLt
  by_cases h64 : j.val < 64
  · by_cases h32 : j.val < 32
    · by_cases h16 : j.val < 16
      · by_cases h8 : j.val < 8
        · by_cases h4 : j.val < 4
          · by_cases h2 : j.val < 2
            · by_cases h1 : j.val < 1
              · have hj : j = ⟨0, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 0
                  omega
                subst j
                exact namedLeaf000_checked
              · have hj : j = ⟨1, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 1
                  omega
                subst j
                exact namedLeaf001_checked
            · by_cases h3 : j.val < 3
              · have hj : j = ⟨2, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 2
                  omega
                subst j
                exact namedLeaf002_checked
              · have hj : j = ⟨3, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 3
                  omega
                subst j
                exact namedLeaf003_checked
          · by_cases h6 : j.val < 6
            · by_cases h5 : j.val < 5
              · have hj : j = ⟨4, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 4
                  omega
                subst j
                exact namedLeaf004_checked
              · have hj : j = ⟨5, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 5
                  omega
                subst j
                exact namedLeaf005_checked
            · by_cases h7 : j.val < 7
              · have hj : j = ⟨6, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 6
                  omega
                subst j
                exact namedLeaf006_checked
              · have hj : j = ⟨7, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 7
                  omega
                subst j
                exact namedLeaf007_checked
        · by_cases h12 : j.val < 12
          · by_cases h10 : j.val < 10
            · by_cases h9 : j.val < 9
              · have hj : j = ⟨8, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 8
                  omega
                subst j
                exact namedLeaf008_checked
              · have hj : j = ⟨9, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 9
                  omega
                subst j
                exact namedLeaf009_checked
            · by_cases h11 : j.val < 11
              · have hj : j = ⟨10, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 10
                  omega
                subst j
                exact namedLeaf010_checked
              · have hj : j = ⟨11, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 11
                  omega
                subst j
                exact namedLeaf011_checked
          · by_cases h14 : j.val < 14
            · by_cases h13 : j.val < 13
              · have hj : j = ⟨12, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 12
                  omega
                subst j
                exact namedLeaf012_checked
              · have hj : j = ⟨13, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 13
                  omega
                subst j
                exact namedLeaf013_checked
            · by_cases h15 : j.val < 15
              · have hj : j = ⟨14, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 14
                  omega
                subst j
                exact namedLeaf014_checked
              · have hj : j = ⟨15, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 15
                  omega
                subst j
                exact namedLeaf015_checked
      · by_cases h24 : j.val < 24
        · by_cases h20 : j.val < 20
          · by_cases h18 : j.val < 18
            · by_cases h17 : j.val < 17
              · have hj : j = ⟨16, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 16
                  omega
                subst j
                exact namedLeaf016_checked
              · have hj : j = ⟨17, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 17
                  omega
                subst j
                exact namedLeaf017_checked
            · by_cases h19 : j.val < 19
              · have hj : j = ⟨18, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 18
                  omega
                subst j
                exact namedLeaf018_checked
              · have hj : j = ⟨19, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 19
                  omega
                subst j
                exact namedLeaf019_checked
          · by_cases h22 : j.val < 22
            · by_cases h21 : j.val < 21
              · have hj : j = ⟨20, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 20
                  omega
                subst j
                exact namedLeaf020_checked
              · have hj : j = ⟨21, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 21
                  omega
                subst j
                exact namedLeaf021_checked
            · by_cases h23 : j.val < 23
              · have hj : j = ⟨22, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 22
                  omega
                subst j
                exact namedLeaf022_checked
              · have hj : j = ⟨23, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 23
                  omega
                subst j
                exact namedLeaf023_checked
        · by_cases h28 : j.val < 28
          · by_cases h26 : j.val < 26
            · by_cases h25 : j.val < 25
              · have hj : j = ⟨24, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 24
                  omega
                subst j
                exact namedLeaf024_checked
              · have hj : j = ⟨25, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 25
                  omega
                subst j
                exact namedLeaf025_checked
            · by_cases h27 : j.val < 27
              · have hj : j = ⟨26, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 26
                  omega
                subst j
                exact namedLeaf026_checked
              · have hj : j = ⟨27, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 27
                  omega
                subst j
                exact namedLeaf027_checked
          · by_cases h30 : j.val < 30
            · by_cases h29 : j.val < 29
              · have hj : j = ⟨28, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 28
                  omega
                subst j
                exact namedLeaf028_checked
              · have hj : j = ⟨29, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 29
                  omega
                subst j
                exact namedLeaf029_checked
            · by_cases h31 : j.val < 31
              · have hj : j = ⟨30, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 30
                  omega
                subst j
                exact namedLeaf030_checked
              · have hj : j = ⟨31, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 31
                  omega
                subst j
                exact namedLeaf031_checked
    · by_cases h48 : j.val < 48
      · by_cases h40 : j.val < 40
        · by_cases h36 : j.val < 36
          · by_cases h34 : j.val < 34
            · by_cases h33 : j.val < 33
              · have hj : j = ⟨32, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 32
                  omega
                subst j
                exact namedLeaf032_checked
              · have hj : j = ⟨33, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 33
                  omega
                subst j
                exact namedLeaf033_checked
            · by_cases h35 : j.val < 35
              · have hj : j = ⟨34, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 34
                  omega
                subst j
                exact namedLeaf034_checked
              · have hj : j = ⟨35, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 35
                  omega
                subst j
                exact namedLeaf035_checked
          · by_cases h38 : j.val < 38
            · by_cases h37 : j.val < 37
              · have hj : j = ⟨36, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 36
                  omega
                subst j
                exact namedLeaf036_checked
              · have hj : j = ⟨37, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 37
                  omega
                subst j
                exact namedLeaf037_checked
            · by_cases h39 : j.val < 39
              · have hj : j = ⟨38, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 38
                  omega
                subst j
                exact namedLeaf038_checked
              · have hj : j = ⟨39, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 39
                  omega
                subst j
                exact namedLeaf039_checked
        · by_cases h44 : j.val < 44
          · by_cases h42 : j.val < 42
            · by_cases h41 : j.val < 41
              · have hj : j = ⟨40, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 40
                  omega
                subst j
                exact namedLeaf040_checked
              · have hj : j = ⟨41, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 41
                  omega
                subst j
                exact namedLeaf041_checked
            · by_cases h43 : j.val < 43
              · have hj : j = ⟨42, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 42
                  omega
                subst j
                exact namedLeaf042_checked
              · have hj : j = ⟨43, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 43
                  omega
                subst j
                exact namedLeaf043_checked
          · by_cases h46 : j.val < 46
            · by_cases h45 : j.val < 45
              · have hj : j = ⟨44, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 44
                  omega
                subst j
                exact namedLeaf044_checked
              · have hj : j = ⟨45, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 45
                  omega
                subst j
                exact namedLeaf045_checked
            · by_cases h47 : j.val < 47
              · have hj : j = ⟨46, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 46
                  omega
                subst j
                exact namedLeaf046_checked
              · have hj : j = ⟨47, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 47
                  omega
                subst j
                exact namedLeaf047_checked
      · by_cases h56 : j.val < 56
        · by_cases h52 : j.val < 52
          · by_cases h50 : j.val < 50
            · by_cases h49 : j.val < 49
              · have hj : j = ⟨48, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 48
                  omega
                subst j
                exact namedLeaf048_checked
              · have hj : j = ⟨49, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 49
                  omega
                subst j
                exact namedLeaf049_checked
            · by_cases h51 : j.val < 51
              · have hj : j = ⟨50, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 50
                  omega
                subst j
                exact namedLeaf050_checked
              · have hj : j = ⟨51, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 51
                  omega
                subst j
                exact namedLeaf051_checked
          · by_cases h54 : j.val < 54
            · by_cases h53 : j.val < 53
              · have hj : j = ⟨52, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 52
                  omega
                subst j
                exact namedLeaf052_checked
              · have hj : j = ⟨53, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 53
                  omega
                subst j
                exact namedLeaf053_checked
            · by_cases h55 : j.val < 55
              · have hj : j = ⟨54, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 54
                  omega
                subst j
                exact namedLeaf054_checked
              · have hj : j = ⟨55, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 55
                  omega
                subst j
                exact namedLeaf055_checked
        · by_cases h60 : j.val < 60
          · by_cases h58 : j.val < 58
            · by_cases h57 : j.val < 57
              · have hj : j = ⟨56, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 56
                  omega
                subst j
                exact namedLeaf056_checked
              · have hj : j = ⟨57, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 57
                  omega
                subst j
                exact namedLeaf057_checked
            · by_cases h59 : j.val < 59
              · have hj : j = ⟨58, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 58
                  omega
                subst j
                exact namedLeaf058_checked
              · have hj : j = ⟨59, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 59
                  omega
                subst j
                exact namedLeaf059_checked
          · by_cases h62 : j.val < 62
            · by_cases h61 : j.val < 61
              · have hj : j = ⟨60, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 60
                  omega
                subst j
                exact namedLeaf060_checked
              · have hj : j = ⟨61, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 61
                  omega
                subst j
                exact namedLeaf061_checked
            · by_cases h63 : j.val < 63
              · have hj : j = ⟨62, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 62
                  omega
                subst j
                exact namedLeaf062_checked
              · have hj : j = ⟨63, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 63
                  omega
                subst j
                exact namedLeaf063_checked
  · by_cases h96 : j.val < 96
    · by_cases h80 : j.val < 80
      · by_cases h72 : j.val < 72
        · by_cases h68 : j.val < 68
          · by_cases h66 : j.val < 66
            · by_cases h65 : j.val < 65
              · have hj : j = ⟨64, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 64
                  omega
                subst j
                exact namedLeaf064_checked
              · have hj : j = ⟨65, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 65
                  omega
                subst j
                exact namedLeaf065_checked
            · by_cases h67 : j.val < 67
              · have hj : j = ⟨66, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 66
                  omega
                subst j
                exact namedLeaf066_checked
              · have hj : j = ⟨67, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 67
                  omega
                subst j
                exact namedLeaf067_checked
          · by_cases h70 : j.val < 70
            · by_cases h69 : j.val < 69
              · have hj : j = ⟨68, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 68
                  omega
                subst j
                exact namedLeaf068_checked
              · have hj : j = ⟨69, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 69
                  omega
                subst j
                exact namedLeaf069_checked
            · by_cases h71 : j.val < 71
              · have hj : j = ⟨70, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 70
                  omega
                subst j
                exact namedLeaf070_checked
              · have hj : j = ⟨71, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 71
                  omega
                subst j
                exact namedLeaf071_checked
        · by_cases h76 : j.val < 76
          · by_cases h74 : j.val < 74
            · by_cases h73 : j.val < 73
              · have hj : j = ⟨72, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 72
                  omega
                subst j
                exact namedLeaf072_checked
              · have hj : j = ⟨73, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 73
                  omega
                subst j
                exact namedLeaf073_checked
            · by_cases h75 : j.val < 75
              · have hj : j = ⟨74, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 74
                  omega
                subst j
                exact namedLeaf074_checked
              · have hj : j = ⟨75, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 75
                  omega
                subst j
                exact namedLeaf075_checked
          · by_cases h78 : j.val < 78
            · by_cases h77 : j.val < 77
              · have hj : j = ⟨76, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 76
                  omega
                subst j
                exact namedLeaf076_checked
              · have hj : j = ⟨77, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 77
                  omega
                subst j
                exact namedLeaf077_checked
            · by_cases h79 : j.val < 79
              · have hj : j = ⟨78, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 78
                  omega
                subst j
                exact namedLeaf078_checked
              · have hj : j = ⟨79, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 79
                  omega
                subst j
                exact namedLeaf079_checked
      · by_cases h88 : j.val < 88
        · by_cases h84 : j.val < 84
          · by_cases h82 : j.val < 82
            · by_cases h81 : j.val < 81
              · have hj : j = ⟨80, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 80
                  omega
                subst j
                exact namedLeaf080_checked
              · have hj : j = ⟨81, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 81
                  omega
                subst j
                exact namedLeaf081_checked
            · by_cases h83 : j.val < 83
              · have hj : j = ⟨82, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 82
                  omega
                subst j
                exact namedLeaf082_checked
              · have hj : j = ⟨83, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 83
                  omega
                subst j
                exact namedLeaf083_checked
          · by_cases h86 : j.val < 86
            · by_cases h85 : j.val < 85
              · have hj : j = ⟨84, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 84
                  omega
                subst j
                exact namedLeaf084_checked
              · have hj : j = ⟨85, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 85
                  omega
                subst j
                exact namedLeaf085_checked
            · by_cases h87 : j.val < 87
              · have hj : j = ⟨86, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 86
                  omega
                subst j
                exact namedLeaf086_checked
              · have hj : j = ⟨87, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 87
                  omega
                subst j
                exact namedLeaf087_checked
        · by_cases h92 : j.val < 92
          · by_cases h90 : j.val < 90
            · by_cases h89 : j.val < 89
              · have hj : j = ⟨88, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 88
                  omega
                subst j
                exact namedLeaf088_checked
              · have hj : j = ⟨89, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 89
                  omega
                subst j
                exact namedLeaf089_checked
            · by_cases h91 : j.val < 91
              · have hj : j = ⟨90, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 90
                  omega
                subst j
                exact namedLeaf090_checked
              · have hj : j = ⟨91, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 91
                  omega
                subst j
                exact namedLeaf091_checked
          · by_cases h94 : j.val < 94
            · by_cases h93 : j.val < 93
              · have hj : j = ⟨92, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 92
                  omega
                subst j
                exact namedLeaf092_checked
              · have hj : j = ⟨93, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 93
                  omega
                subst j
                exact namedLeaf093_checked
            · by_cases h95 : j.val < 95
              · have hj : j = ⟨94, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 94
                  omega
                subst j
                exact namedLeaf094_checked
              · have hj : j = ⟨95, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 95
                  omega
                subst j
                exact namedLeaf095_checked
    · by_cases h112 : j.val < 112
      · by_cases h104 : j.val < 104
        · by_cases h100 : j.val < 100
          · by_cases h98 : j.val < 98
            · by_cases h97 : j.val < 97
              · have hj : j = ⟨96, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 96
                  omega
                subst j
                exact namedLeaf096_checked
              · have hj : j = ⟨97, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 97
                  omega
                subst j
                exact namedLeaf097_checked
            · by_cases h99 : j.val < 99
              · have hj : j = ⟨98, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 98
                  omega
                subst j
                exact namedLeaf098_checked
              · have hj : j = ⟨99, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 99
                  omega
                subst j
                exact namedLeaf099_checked
          · by_cases h102 : j.val < 102
            · by_cases h101 : j.val < 101
              · have hj : j = ⟨100, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 100
                  omega
                subst j
                exact namedLeaf100_checked
              · have hj : j = ⟨101, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 101
                  omega
                subst j
                exact namedLeaf101_checked
            · by_cases h103 : j.val < 103
              · have hj : j = ⟨102, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 102
                  omega
                subst j
                exact namedLeaf102_checked
              · have hj : j = ⟨103, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 103
                  omega
                subst j
                exact namedLeaf103_checked
        · by_cases h108 : j.val < 108
          · by_cases h106 : j.val < 106
            · by_cases h105 : j.val < 105
              · have hj : j = ⟨104, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 104
                  omega
                subst j
                exact namedLeaf104_checked
              · have hj : j = ⟨105, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 105
                  omega
                subst j
                exact namedLeaf105_checked
            · by_cases h107 : j.val < 107
              · have hj : j = ⟨106, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 106
                  omega
                subst j
                exact namedLeaf106_checked
              · have hj : j = ⟨107, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 107
                  omega
                subst j
                exact namedLeaf107_checked
          · by_cases h110 : j.val < 110
            · by_cases h109 : j.val < 109
              · have hj : j = ⟨108, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 108
                  omega
                subst j
                exact namedLeaf108_checked
              · have hj : j = ⟨109, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 109
                  omega
                subst j
                exact namedLeaf109_checked
            · by_cases h111 : j.val < 111
              · have hj : j = ⟨110, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 110
                  omega
                subst j
                exact namedLeaf110_checked
              · have hj : j = ⟨111, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 111
                  omega
                subst j
                exact namedLeaf111_checked
      · by_cases h120 : j.val < 120
        · by_cases h116 : j.val < 116
          · by_cases h114 : j.val < 114
            · by_cases h113 : j.val < 113
              · have hj : j = ⟨112, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 112
                  omega
                subst j
                exact namedLeaf112_checked
              · have hj : j = ⟨113, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 113
                  omega
                subst j
                exact namedLeaf113_checked
            · by_cases h115 : j.val < 115
              · have hj : j = ⟨114, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 114
                  omega
                subst j
                exact namedLeaf114_checked
              · have hj : j = ⟨115, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 115
                  omega
                subst j
                exact namedLeaf115_checked
          · by_cases h118 : j.val < 118
            · by_cases h117 : j.val < 117
              · have hj : j = ⟨116, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 116
                  omega
                subst j
                exact namedLeaf116_checked
              · have hj : j = ⟨117, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 117
                  omega
                subst j
                exact namedLeaf117_checked
            · by_cases h119 : j.val < 119
              · have hj : j = ⟨118, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 118
                  omega
                subst j
                exact namedLeaf118_checked
              · have hj : j = ⟨119, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 119
                  omega
                subst j
                exact namedLeaf119_checked
        · by_cases h124 : j.val < 124
          · by_cases h122 : j.val < 122
            · by_cases h121 : j.val < 121
              · have hj : j = ⟨120, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 120
                  omega
                subst j
                exact namedLeaf120_checked
              · have hj : j = ⟨121, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 121
                  omega
                subst j
                exact namedLeaf121_checked
            · by_cases h123 : j.val < 123
              · have hj : j = ⟨122, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 122
                  omega
                subst j
                exact namedLeaf122_checked
              · have hj : j = ⟨123, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 123
                  omega
                subst j
                exact namedLeaf123_checked
          · by_cases h126 : j.val < 126
            · by_cases h125 : j.val < 125
              · have hj : j = ⟨124, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 124
                  omega
                subst j
                exact namedLeaf124_checked
              · have hj : j = ⟨125, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 125
                  omega
                subst j
                exact namedLeaf125_checked
            · by_cases h127 : j.val < 127
              · have hj : j = ⟨126, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 126
                  omega
                subst j
                exact namedLeaf126_checked
              · have hj : j = ⟨127, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 127
                  omega
                subst j
                exact namedLeaf127_checked

theorem correct (id : Fin 24698) (hlow : 5120 ≤ id.val) (hhigh : id.val < 5248) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 5120)) = true := by
  let j : Fin 128 := ⟨id.val - 5120, by omega⟩
  have hsum : 5120 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (5120 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard040
