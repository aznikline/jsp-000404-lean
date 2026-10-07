import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard045
open N4R2OuterLeftReplay

-- Cycle fingerprint 003d5261c1c702a36807cacdf19d10e71a6035b5324d1e3191287fc972ea7a9c.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .triangle 9 0, .triangle 5 1, .corridorLower 2 3]

-- Cycle fingerprint 0407ca5a506ee07a3cd3cb91f6e63e24dee8c9cc53ce7cb6c04dbd181f3d4b4e.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 04b5c6c58d301c9863cbe4fe6cda8c2be74dc24c9965bb94e5946d36d3c09267.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 06cf1db936c7bcbcc6d1932083626716ef21ae434426147db8a6e55ec3b9cc27.
def localCycle00003 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 07e572c14056dac5e6cd1acfbc3e02d1653cb4d04e76ff6b9b943d509e6fb059.
def localCycle00004 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 20 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0bb76ff8f2aa7a8f2b10cbbda77785243e5e8df3093b9c919d19daa9eecff5c0.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .gapLower 5 0]

-- Cycle fingerprint 0be961b25cc229563c6cba0056560d1842fcb7bc0b385d13f18362d915b703a1.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0c41b1c874788fe21a68e186c5734c18c5decc9222e3a0a9ab6a8a669d1e277c.
def localCycle00007 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 5]

-- Cycle fingerprint 0c9cc4a3d14b1c2448c12a3bfab0dd9989123a0b52ea369bbff90a8f52972d96.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 0 2, .triangle 5 0, .triangle 26 0, .gapLower 5 0]

-- Cycle fingerprint 174add3fde5153f702ed9ba55a83bcf6a016128b60e57056515dd6d33270c2d2.
def localCycle00009 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 174d9cdc31681b43f086779018c1a89829f8e9f198eae8fae92119993c8a47c7.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 179a15423f78cdd46a72d0d01360f414ab27c6217c8ab977c571ed6ef104ade6.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .gapLower 4 0]

-- Cycle fingerprint 1daee5f24d38d73aab328c120035685071a8b504dd3915e8596ec83b47af31d5.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 1faf8182d1e9e37296d72792498b19517d7a65af86c7a0f506da01de7f9587be.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 22f11f46f4d0ef097ea287421f3e17fa39a756cf0d93728749404a1ff3a17f4c.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .zero, .theta 6, .distance 0 6, .distance 0 4]
    constant := ![-1, -1, 0, -1, 0, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true, true] }
  origin := ![.triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 13 1]

-- Cycle fingerprint 258626a6dced3791c4f0bc1504e89a1db68e83a837449ee8ef98e17bd4d8db0f.
def localCycle00015 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .triangle 8 0, .triangle 7 0, .gapLower 5 0]

-- Cycle fingerprint 2aa6d756dee452ead355cf0fe71d7a01e3cb373ece82c6efa2fd42f92c084895.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 3, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 2af71584599cd2c1e4b83ae593a98fde5023d76521d423b9691ffa541464f7f1.
def localCycle00017 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 2fcfcc87cce986f59eed78d4e7032540685e1645c590bff0bfba401fb907cbfc.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 311bc98313541b514ddd51aaec2edac44ed69ba3f7686b4d354fdbfa4fc884d8.
def localCycle00019 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .gapLower 6 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 31c2206412be8aafa78cbeead9f69e0a25752ac8f89e8fe08edf9d5aa5eaecd2.
def localCycle00020 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 3207857e354856f90f4c04e5d854f7b0e769b36c5daea2796c6c08cc0c5d0cea.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true] }
  origin := ![.triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 2, .gapUpper 2 5]

-- Cycle fingerprint 32e97fd15019c96edd440cca592e1d318f189b31ef9a3ec115c9b6a727cae9e1.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 3334f61181f84ca6e4c6036b1604aaa2f5ab8990871257e273d695b2c33754d9.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint 35ab7c65cb86016b07b7f1b51e6b17bcb336e7fa061931938067a5a905767461.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 3686e7d86d001714ee6548897894ad65cb8ac3e38cdcc32e6a7015fda7b0d707.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 3a4b9f312fdc4962748d3b2bf8691933a9697e9dc09856a433e4742fea5192e8.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 3f7f89f4b8646d80a0384fff0f6da3e6ad3026b7379d1334cba472f0671fe79c.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .gapLower 4 0]

-- Cycle fingerprint 4319aeb8c1ad173272cdb8359b694b00b916c3891475629017c24eda3f68db0a.
def localCycle00028 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 43405380b529ba9c112505690152a33eec21de31ec0f32508c70ff5801bf01f7.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 43e56878b7c388b866c986ea3a183b92bfc2f852337e2db287985c606a7209b4.
def localCycle00030 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 4595c2b8124363506a5ed82007d94208352021cc939f176da30925c395c8a605.
def localCycle00031 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Cycle fingerprint 485a5a323a8128af800c0ae60014c2f04301ca5d69c9c753d3c70855a766bea9.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5]
    constant := ![-1, -1, 0, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0]

-- Cycle fingerprint 4a7d84485449982a07519e23c465e3436792f4d3ab5e6612050f672fb4f44ef2.
def localCycle00033 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 4d18e718e013cc3515d557355fb3a6fea6e04f01909bb18fea34218972360d5b.
def localCycle00034 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 5003a14fa64f7bad33fce7126b5633ba44fd198afb1bb0fc3158d677803af245.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 52de348cbb225a94e2df097687315320de1d86f08f20619ee647d1a1aa235f2a.
def localCycle00036 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 550fe7e7b99cf659cfa99a3d5edde8c11360c175f0302ee9c6c9cd31299d6b6c.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 55a138bcc45325fa55902a0c070c7a129e8a85f63832c3c3a7ce69c6f06f60b7.
def localCycle00038 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 5805db678bf6328c92a9511dccf3257a296f05357e0cb0c020fe50fb733f69df.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 58aa70a58bdf4666443b156970c82435fd2c825ba8d49f7e0f93fde1422c7625.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 3, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 5b98ad77a34068531d4908f9ee6c6b42ec6e086347f398d939605730c4e9211d.
def localCycle00041 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 5f93ab30f7e3049e0fa0d7e19aaace070f871b67125ba77226deb65b4d4f708d.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6127bf8e17c7aff901126dd5f487416b0f8735eb20d782f1584b82709f33347a.
def localCycle00043 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 66b00e1f8e20fad45620c927ebb2913f1f8e51e69799db285f10dd48eb68654f.
def localCycle00044 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 6735fd257c88bf910b4fa8ce18a6a846afacbdce1000b5ec4087e8d9f5754833.
def localCycle00045 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 67fc07b755c9a2d17e869c1ad5ea8a2b202b0ec1719fd289106ed435c443f8df.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 694047e6014902fc144cd77870340bf9ed3d5373ebc347cba453a50746cf1496.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 6a663c36c5ded82e3deb491c8fffe572260607db100fa2ebc613a05c4b77d963.
def localCycle00048 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 20 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 19 0]

-- Cycle fingerprint 6b0b54b63bcbe2b445dbbc57047247ba84ff8c7d1bdaf7c85528e7f25952c512.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 6de45e4582c9faa37dc4c7e7381cab853154f42cb3ce757fb664ae33f052bc54.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 6fca8e486e2657541664382a7b6ab3dd27c913bddcf93a6e145f8886e301c37f.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 71fed7432ddc8cd50cb280d16f5b680efb3be3b1f2577219ca26d9807da87a33.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 735b157c64635593ae9ca8068fce363f79bbbe828fa202307c668d25bfc601e9.
def localCycle00053 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 7393fb2e5cb27393d8ee6b47c3ecccae65dae0e161d3eb5ed4ab2de8c894ee1d.
def localCycle00054 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 758cd42858233c6d14e516966db962ac901a74f41545f8088df7d51bc43f9607.
def localCycle00055 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 76e44a8fbd02ccf3d95a95609e1a463370902baf7ca9cd830791f39bd0a20cc1.
def localCycle00056 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 77002ded749b7c5657533ac1b87de2a9b09ee89e45a2b61ba5b7bb2c85e96bd4.
def localCycle00057 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 7bfe70b611d07ab75d419e5fb857b47a774a7be685f28a1cd0238d28ca7f23c0.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 7ce558c26338b5d11dc3b6e549cfb197c920b9ab7542eca536a00b5b965d31c4.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 7d056ee64be542c24b2676d77d9516b2854bf0443ab2adf0b6f9f1111f5789af.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 7f66b80b52a68bd700eaa3d53603af2f54d215e45eb0c5de1f39e6a13a912a3e.
def localCycle00061 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 8243f0965fc4f26d1354aca81a312e5c1d30218ac041bbc0bfb3c4229bed3ef3.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![0, -1, -1, 0, 0, 3, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0]

-- Cycle fingerprint 8a535ae9c7f59320b455f36151b11fc507250e4685c9249d8cb51a77b89a3d79.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 8f8017ab585073dd0934867f062689faa27fe8b170b0fd93b30b6a49b7d0177b.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 94f66ff0f87c5a2fa6a0a0e8219f3069b48a2e6aae0fad1702358049fd1cac39.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 98e76b9fc5a0dc26a5916ef54198df39bb27dd9763d877b2e69962582736ef03.
def localCycle00066 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 9b345c9e2612c07f9a70ff656f8f04b2c1fe77599970ba0f2ffb49292ab5f190.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 9fe4b280c92f24eb54e5abd7c12de2ab6544e45086b10b8680c11e7a498bd8c6.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a039344ca4275a24557fe6cc428c8bf08e59623340a008fd9e5a905198621977.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 2, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 11 1, .triangle 9 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Cycle fingerprint a2b5e95f55f041ae68558a445b0688a9b8e02ab61c6dbc6926b7a121ecd79f9c.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 2, .triangle 18 1, .triangle 8 0, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint a6785b3b0d42702ccd87a71428d255b0e46136834fb70e8a28ab6d7583576302.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 8 1, .triangle 7 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint ab656db88cabfdb807624b02d04a6cd558b723cbf91ae0e0289e84eddf86f27a.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint adf3fc1984556dd490c91e6e7f1c9e9c63c8f81dea8b3ef384f39583a15e64cb.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint aecb2d918605fa20293f587f39f4ce66f1aae79c5fb689ea09f3a2ff75429ac4.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b1f202da5792a9954462995384331b155d539424ea94c35f808340465a58f02d.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint b49066b4812c377b27cd51ae981425904761bacdac7bcaad0ab25e38e391904d.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint bbc01e1a3028ab5ec491b5fbef63861bd36f628df8e538f618c4b16ba51bfec4.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint beac32d9aa135a9b75bad75fc4f6562f705019171ab5aa514311c20b83b32cc9.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint c12890609903210cbba87f69db414630401aa4ce8f95f2bf1bd60bc4c47d55c9.
def localCycle00079 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint c1e5ef9fa4ed870c7212be36770849ff541e07c6429031fd3f9084c4caf9db69.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 28 2, .triangle 26 1, .corridorLower 2 3]

-- Cycle fingerprint c386ca6452411dc768e91ba062fdc8a06415d19340edc5f63b58812651f3496c.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .gapLower 4 0]

-- Cycle fingerprint c87be0a65f28cc6af32fee5dba91d9c9c7b120b3a58ecdff1e4b0c261feed675.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint c9b4ee8eaf5e80ffa55ff3eb37118cec8a93e00c6e57c2edc52ce86e3c86ae49.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint cb11f078cb63df346bf6d3ee044f8f699c1de521b1c36522e4402f1280d89254.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint cb4ac271c5879b05a0c816046af45254c377012a891a6e8339159a0cc6ce83c3.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint cc7cf024463085dd2a5ab402e6405dbdd5ddc79cecb4548df99dcae118beeef9.
def localCycle00086 : Cycle where
  length := 13
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint ccb2762e0d8d1d6185d5f4a22d2081fdb00133f4ea8668763233848133523d05.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d0f9767f684699e7519b1d1045f311fb9a4ef0a671838cb990996966483543a1.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint d3e7cc20abaa2b1d27553070e7d87db18982f6804ac83d84ba4906c55cb10d1a.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint d62b5a17a3fa3d1d938e3e1b182a465043fd11e9ada8192967851edafcd5d212.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true] }
  origin := ![.triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 5]

-- Cycle fingerprint e1d0675277e9fd14f0539c204d5c468269f58537a519ecb84122a94e1110eab0.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint e36dbcc08239a74dc390238b95eace2e8b0814a49b27ee98e4f8a2b431b88f01.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint e4164260ce9232b7389bcf6779680f9e1d833f1199711be346d821da06419e86.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint e53797ba7943d349444233a71cde9c1604b5ebec9cce8fd43f2d0c1b7de144d3.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e672062f4b3269a0fc4c6ad39af7874a649050c76b445e97dad5600aec83460c.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .zero, .theta 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaLower 3, .thetaUpper 6, .gapUpper 6 0, .triangle 8 1, .triangle 6 0, .triangle 28 0]

-- Cycle fingerprint ec6106683d7baa41d0a1b4ff9c85e8dfa5b8aa247c3b6d8874759e9a0bb1530d.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint eec8d711ff2bf0d31fa94cfde87c07535e2adf890dfce257c65779b55d726910.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint f2a97f22df1074f953df486dad6213d65bf757574abc6270641ecd51d713d441.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint f32bc52cdbae62baa1fc82b91922b36b23964f34afd6e3360de99f065d085310.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 0 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 8 1, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint f372f289f648366fe2a447275a1eb39df440fa6b21ca4b1409ca1c320a870d04.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint f39e6d33a04b4228da13350c5a9efbf22d31c1533509681d2ae2232b80893f7a.
def localCycle00101 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint f40e303c3664d44cc3309f99ecf9f63c6e784072d7de68abb819437d2c2f4e7c.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint f447d0916db96301218f73e729ff346a27bbe8245829c2ad935e824a151324f6.
def localCycle00103 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint f471623b58520db94ffedd9ce91baee564f9fe4b5334e891353bbe2cc3b13177.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint f4dc4b884f06eff7ce21ff65a8f878f2db8e972aa2deb56600e415a620cc3b70.
def localCycle00105 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint f867fe0ae390251565815951b1def631df85e1fbddca52ebc5341912634d4a5e.
def localCycle00106 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 0, 3, -1, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true, false] }
  origin := ![.thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 6 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint fe3efefc404c86886680f9dbe12a24353a5d408c01ba9f192488067612de522a.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint fe644415666a9a696111f771ae53314a047e761f587ce12106817de0e941a539.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .gapLower 4 0]

def library : Library := fun id => if id < 54 then (if id < 27 then (if id < 13 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))))) else (if id < 20 then (if id < 16 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))) else (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)))) else (if id < 23 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none))) else (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))))) else (if id < 40 then (if id < 33 then (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)))) else (if id < 36 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))) else (if id < 38 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))))) else (if id < 47 then (if id < 43 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)))) else (if id < 50 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))) else (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))))))) else (if id < 81 then (if id < 67 then (if id < 60 then (if id < 57 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)))) else (if id < 63 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))) else (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none))))) else (if id < 74 then (if id < 70 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))) else (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))) else (if id < 77 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))) else (if id < 79 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)))))) else (if id < 95 then (if id < 88 then (if id < 84 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)))) else (if id < 91 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))) else (if id < 93 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))))) else (if id < 102 then (if id < 98 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))) else (if id < 100 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)))) else (if id < 105 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))) else (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 5, 4, 1, 6], ![2, 5, 0, 3, 1, 6], ![2, 4, 0, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 30 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5760)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 0, 5, 4, 1, 6], ![5, 2, 0, 3, 1, 6], ![4, 2, 0, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 95 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5761)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 5, 3, 4, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 5, 0, 4, 1, 6], ![2, 5, 0, 3, 1, 6], ![2, 4, 3, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 43 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5762)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 5, 3, 4, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 5, 0, 4, 1, 6], ![5, 2, 0, 3, 1, 6], ![4, 2, 3, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 43 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5763)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 5, 3, 4, 2, 6], ![0, 5, 4, 3, 2, 6], ![5, 3, 4, 0, 1, 6], ![5, 2, 0, 4, 1, 6], ![5, 2, 0, 3, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 25 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5764)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 93 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5765)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 9 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5766)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 37 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5767)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 73 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5768)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 55 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5769)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 28 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5770)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 5, 0, 1, 6], ![2, 3, 0, 1, 5, 6], ![2, 3, 0, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 98 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5771)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 5, 0, 1, 6], ![2, 3, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 41 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5772)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 5, 0, 1, 6], ![2, 3, 0, 5, 1, 6], ![2, 3, 0, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 82 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5773)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 5, 0, 1, 6], ![2, 3, 5, 0, 1, 6], ![2, 3, 4, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 72 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5774)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 5, 4, 0, 1, 6], ![2, 5, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 36 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5775)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 5, 4, 0, 1, 6], ![5, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 69 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5776)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![5, 3, 4, 0, 1, 6], ![5, 2, 4, 0, 1, 6], ![5, 2, 3, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 83 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5777)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 71 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5778)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 101 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5779)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 33 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5780)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 5, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 35 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5781)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 5, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 57 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5782)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 5, 4, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 60 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5783)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 0, 1, 6], ![3, 2, 0, 1, 5, 6], ![2, 3, 0, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 47 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5784)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 0, 1, 6], ![3, 2, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 53 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5785)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 0, 1, 6], ![3, 2, 0, 5, 1, 6], ![2, 3, 0, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 60 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5786)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 0, 1, 6], ![3, 2, 5, 0, 1, 6], ![2, 3, 4, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 1 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5787)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 99 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5788)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 8 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5789)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 99 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5790)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 14 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5791)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![5, 4, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 38 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5792)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![5, 4, 3, 0, 1, 6], ![5, 4, 2, 0, 1, 6], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 31 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5793)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 68 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5794)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 42 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5795)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 97 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5796)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![2, 0, 1, 6, 3, 4], ![0, 2, 1, 5, 4, 3]], proof := .tail 62 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5797)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 3, 6], ![2, 0, 1, 4, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 87 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5798)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 3], ![2, 0, 1, 4, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 97 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5799)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 5, 6, 3], ![2, 0, 1, 4, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 94 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5800)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![2, 0, 1, 6, 4, 3], ![0, 2, 1, 5, 4, 3]], proof := .tail 32 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5801)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 63 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5802)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 1, 4, 3]], proof := .tail 19 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5803)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![2, 0, 6, 1, 4, 3], ![0, 2, 5, 1, 4, 3]], proof := .tail 27 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5804)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 4, 1, 3]], proof := .tail 65 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5805)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![2, 0, 6, 1, 4, 3], ![0, 2, 5, 4, 1, 3]], proof := .tail 81 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5806)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 4, 6], ![2, 0, 5, 1, 3, 6], ![2, 0, 4, 1, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 97 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5807)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 1, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 64 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5808)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 1, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 56 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5809)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 1, 3, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 2 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5810)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 1, 6, 3], ![0, 2, 4, 1, 5, 3]], proof := .tail 2 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5811)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 6, 1, 3], ![0, 2, 4, 5, 1, 3]], proof := .tail 84 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5812)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 0, 6, 4, 1, 3], ![0, 2, 5, 4, 1, 3]], proof := .tail 91 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5813)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 4, 3, 1]], proof := .tail 5 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5814)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![2, 0, 6, 1, 4, 3], ![0, 2, 5, 4, 3, 1]], proof := .tail 81 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5815)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 6, 1, 3], ![0, 2, 4, 5, 3, 1]], proof := .tail 66 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5816)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 0, 6, 4, 1, 3], ![0, 2, 5, 4, 3, 1]], proof := .tail 11 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5817)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 3, 6], ![2, 0, 4, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 48 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5818)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 3, 1, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 106 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5819)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 3, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 1, 6, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 3, 1, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 2 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5820)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 6, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 59 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5821)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 17 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5822)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 5, 1, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 20 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5823)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 3], ![2, 0, 6, 4, 3, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 108 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5824)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 67 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5825)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 24 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5826)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 4 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5827)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 3, 6, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 63 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5828)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 6, 3, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 61 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5829)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 6, 1, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 49 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5830)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 4, 1, 5], ![2, 0, 6, 3, 1, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 4, 3, 1]], proof := .tail 15 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5831)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 97 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5832)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 45 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5833)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 74 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5834)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 1, 6], ![2, 0, 5, 3, 1, 6], ![2, 0, 4, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 76 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5835)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 12 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5836)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 12 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5837)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 1, 6, 5], ![2, 0, 3, 6, 1, 4], ![0, 2, 3, 5, 1, 4]], proof := .tail 16 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5838)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 1, 6, 5], ![2, 0, 6, 3, 1, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 26 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5839)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 6, 1, 5], ![2, 0, 3, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 49 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5840)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 1, 5], ![2, 0, 6, 3, 1, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 6 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5841)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 1, 5], ![2, 0, 6, 3, 1, 4], ![0, 2, 5, 4, 3, 1]], proof := .tail 103 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5842)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 74 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5843)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 0, 5, 3, 1, 6], ![2, 0, 4, 3, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 51 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5844)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 5, 6, 1], ![2, 0, 3, 4, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 78 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5845)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 0, 5, 3, 6, 1], ![2, 0, 4, 3, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 13 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5846)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 3, 1], ![2, 0, 4, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 58 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5847)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 5, 6, 1], ![2, 0, 3, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 0 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5848)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 6, 5, 1], ![2, 0, 3, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 40 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5849)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 5, 1], ![2, 0, 6, 3, 4, 1], ![0, 2, 5, 3, 4, 1]], proof := .tail 44 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5850)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 5, 1], ![2, 0, 6, 3, 4, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 90 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5851)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 0, 5, 3, 6, 1], ![2, 0, 4, 3, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 10 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5852)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 3, 1], ![2, 0, 4, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 58 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5853)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 5, 4, 1], ![2, 0, 5, 6, 3, 1], ![2, 0, 4, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 21 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5854)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 3, 1], ![2, 0, 6, 4, 3, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 7 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5855)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 29 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5856)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 39 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5857)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 105 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5858)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 1, 3, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 89 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5859)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 1, 6, 3], ![0, 2, 4, 1, 5, 3]], proof := .tail 89 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5860)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 6, 1, 3], ![0, 2, 4, 5, 1, 3]], proof := .tail 88 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5861)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 1, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 6, 1, 3], ![0, 2, 4, 5, 3, 1]], proof := .tail 23 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5862)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 1, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 0, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 100 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5863)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 1, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 3, 1, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 92 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5864)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 1, 6, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 3, 1, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 77 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5865)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 6, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 1, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 102 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5866)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 1, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 96 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5867)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 5, 1, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 107 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5868)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 1, 6], ![2, 5, 0, 3, 1, 6], ![2, 4, 0, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 30 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5869)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 5, 0, 3, 1, 6], ![2, 4, 0, 3, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 75 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5870)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 5, 0, 3, 6, 1], ![2, 4, 0, 3, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 85 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5871)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 0, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 104 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5872)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 5, 0, 3, 6, 1], ![2, 4, 0, 3, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 54 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5873)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 0, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 104 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5874)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 5, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 0, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 46 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5875)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 1, 5, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 0, 1, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 80 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5876)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 34 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5877)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 70 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5878)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 6, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 1, 3, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 3 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5879)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 6, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 1, 6, 3], ![0, 2, 4, 1, 5, 3]], proof := .tail 18 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5880)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 6, 5, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 6, 1, 3], ![0, 2, 4, 5, 1, 3]], proof := .tail 22 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5881)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 3, 5, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 6, 1, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 6, 1, 3], ![0, 2, 4, 5, 3, 1]], proof := .tail 50 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5882)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 5, 1, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 0, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 79 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5883)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 5, 1, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 3, 1, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 86 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5884)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 6, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 5, 1, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 3, 1, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 3 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5885)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 6, 3, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 5, 6, 1, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 50 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5886)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 5, 3, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 5, 6, 1, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 52 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5887)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (5760 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 5760 ≤ id.val) (hhigh : id.val < 5888) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 5760)) = true := by
  let j : Fin 128 := ⟨id.val - 5760, by omega⟩
  have hsum : 5760 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (5760 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard045
