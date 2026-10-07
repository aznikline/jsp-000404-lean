import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard165
open N4R2OuterLeftReplay

-- Cycle fingerprint 0277d85dcb7ccaf8fbc2ecc05f060c19d8342a830e47a26a875b5e083caff50c.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-2, -2, -1, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .triangle 18 2]

-- Cycle fingerprint 02fa9f8f6d7e627006da2a0e2fc6b9365d2b47d0d79397fc31545a1c6677a15c.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 6]
    constant := ![0, -1, -1, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true] }
  origin := ![.triangle 11 1, .triangle 9 0, .triangle 19 0, .corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 2]

-- Cycle fingerprint 03df58b17e38567e614e21477670a0d8919b01e0faf87b11e05be65141a9a23f.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6]
    constant := ![-1, -1, -1, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2]

-- Cycle fingerprint 07231ae61fb6d95e71406d41130954f16466c8279a8c59479941ebee6fa88227.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-1, -1, -2, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 8 0, .triangle 18 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0]

-- Cycle fingerprint 09d97da0a7001de6195c1b508ef6093f3eee750989007bb0bbe8014901554e5d.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 3, .distance 3 4, .theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6]
    constant := ![0, -2, -1, -1, 4, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 8 0]

-- Cycle fingerprint 09fdedc50c013b327587da11cd783c27cfe81373ba4e1a915d6cf9bbfe167a1a.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 4, .theta 3, .distance 3 5]
    constant := ![0, -1, -1, 0, -2, -1, 0, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 5 4, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 1 3, .triangle 19 0, .gapLower 3 0, .gapLower 3 6]

-- Cycle fingerprint 13b36f4a2ce8197911b70aa3fc915779a255122a8c6e4bc8cde4a945877636db.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 17 1, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 18e29c27f9ae3e39c24d6922278e2fca2f503062b250ca3f6979e8b42c84cc2a.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 1adfe2bd8030e496baef010bfea388838a49b1e456116b3a2e5b542be99b7cea.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 1b7549f6c95cd062a976b2544e174d539b550277c12cf67c50047385615323c5.
def localCycle00009 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 6, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 17 1, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 1fbdb0f46e6caf4bd1b6ba7d2d87e5a599bbd8907c3c547a233672d7eeb3ad97.
def localCycle00010 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -1, 0, 0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 20fa2ed9e6df2015707d74873f9d5ad52b4f507451b865c5899533861d3afa3e.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, 0, -1, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 5 2, .triangle 9 0, .triangle 19 0, .gapLower 1 0]

-- Cycle fingerprint 2526a229cf707470781d74d48e39d0da716fd5c5c1629759077cf3faf07fc412.
def localCycle00012 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 5]

-- Cycle fingerprint 2611895b53843fa9b7dd022901083e2f579211a0fde24463f6445df3b86c4a8c.
def localCycle00013 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 277307c5e04da0238746be19ac28c22c1cc60d3b70dbffd5b2b83c52bf3801fc.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 279244794dae779ccffa350ef4c1d2279473186e9ac4efe65e6e0f4c3a99e153.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 5 2, .triangle 9 0, .triangle 19 0, .corridorLower 1 3]

-- Cycle fingerprint 2a6fe72c868efe230d23f092f6dd712ddd1888ab74d5458f8ce6a339c5eb4c01.
def localCycle00016 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, -1, 0, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 2de08b56557a560f36d8dd379d3ef6d6462097e114567a076655b56ff99ddf0a.
def localCycle00017 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 6, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .corridorUpper 0 1, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 2f95e71dec2ef0ccc678add4b848e34e2a3f13189417f9db8a7780c7d6de5204.
def localCycle00018 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 4]
    constant := ![-1, -2, 0, 0, 3, 0, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, false] }
  origin := ![.triangle 19 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .triangle 11 1, .triangle 9 0]

-- Cycle fingerprint 326e8db34ffc0b32d7057e2f25a5b2993732dfeda7fa75d4f65416ec30191a30.
def localCycle00019 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, -1, 0, -1, 3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 19 0, .corridorLower 1 3]

-- Cycle fingerprint 364359bdca56063752587979ae8e8b66baa5f98995b802c3932514482da7a9ab.
def localCycle00020 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 3993ea2059cb0360133c2c6d1189ad9752bf1f0d6ca9669b07677f47a3ada775.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6]
    constant := ![0, 0, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 18 2, .triangle 21 1, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 0]

-- Cycle fingerprint 3ab9e4b701dd1da4ffa570cbfd68e38471ce3055fd89b0034397e774b7b400b6.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 3bd1dc9750982b9ead6bb9dee0356d18478aa52b59b1d4d12d1a54dd6e77cd3e.
def localCycle00023 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 3db16bcf4866b97de4bed96e5c5acd47724bfffe2137c08dcc7737fcf76bf759.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, -1, 4, 0, -1, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 16 0, .triangle 25 1, .corridorLower 3 4, .gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 21 0, .gapLower 1 2]

-- Cycle fingerprint 3eb5bc63179596ebd4a2646c8bfbd007a373ffcc84d86b44cde0cf2d3208c951.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6]
    constant := ![-1, -3, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 18 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0]

-- Cycle fingerprint 3ff387b568267d34a9d7cee77ee3cd620edbe33e9593d12d86bf7ed579860541.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 401b2a7ebf448c485e08d6d8177319aab21e74cd3ec4a3bfe1205b7d14510826.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 41dec66549e0524f171aa90b52fd40c35aca2a5c0ab8e7eb1a80acbb52cb7ed0.
def localCycle00028 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 2, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 425764b89f2076e3a9ee715be8ee0facf601431657e49a04cc4bfc8396b14ae1.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 6]
    constant := ![0, -1, -1, -1, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true] }
  origin := ![.triangle 11 1, .triangle 9 0, .triangle 19 0, .corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 2]

-- Cycle fingerprint 428b8acb6cc59e70784b9e0b52bc1f0cce0468acb5197b5dc06eae3357c40711.
def localCycle00030 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-1, 4, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 3 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 4322faae378d2abeb5be5e35a345cfaa3ba1116bf2ceb2ae778fdf335b716b34.
def localCycle00031 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 4462187b71870a9d414947e46b2c49b0b196cc3e49126343b032a75094f766b7.
def localCycle00032 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![0, -1, -1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 7 1, .triangle 5 0, .triangle 15 0, .gapLower 1 0, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint 45185afb7c150cf833a8a1250cc801b4f5180d07d605c5ec5802b4bbbccc35ea.
def localCycle00033 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 18 2, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 4548e5d814fbee3c31f7ffcc54945a99db051403e624c9e076a9e7ba6e32c190.
def localCycle00034 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .triangle 25 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 47b8530fd21aab860d4ed48056ff37c7b690e12492a1025d68ad03504eaba447.
def localCycle00035 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 18 0, .triangle 30 1, .gapUpper 5 1]

-- Cycle fingerprint 481c61bdde90ec8eac114fee371b68e5cf7255b4e3a4042006bdc182b63cbe63.
def localCycle00036 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 489ee96d111df7157800dfb20c8bc43aadfa7dc06b9d23debca960d57733a725.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 49236715e242a4ef7b3ea148965e7de8a0270f71c64d3d3da8874cb5bdfc60a4.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, -1, -1, -1, 2, -2, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5]

-- Cycle fingerprint 4f0373d2b03d49ead0182153158bdc6f7598cd47afcfef4eb9f1854d24323df2.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 50aa8d60456dac2ee5b80ac40ee09f14f536c4987c0e4df2f7ef009c7f23cc52.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 518f996228318fe054503c93e2956d9a6c83de4da82fa9dd20b7f710b556b162.
def localCycle00041 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![0, 0, -1, 0, -2, -2, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 8 2, .triangle 11 1, .triangle 9 0, .triangle 19 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0]

-- Cycle fingerprint 5377eaca9868ff7fc3d3a3c4745bbc36ffc677627eb35bd85ab18adfb5c5b9cb.
def localCycle00042 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0]

-- Cycle fingerprint 54722a95e48c2e0c36abfbe3b72c927d9dd30fe8a1a3329eaf83f4979b070c96.
def localCycle00043 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 57ea5e9ff81e33a96dee0659176b5877677f8efe73053ec7f5288ced4eb75e0d.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3]
    constant := ![-1, 2, 0, 0, 0, 0, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 2, .triangle 11 1, .triangle 9 0, .triangle 19 2, .gapLower 1 1]

-- Cycle fingerprint 584360cb3d8f3163b2ff4d12e135d6c04718f303ee8cf7ea764d22ea276e95aa.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 19 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0]

-- Cycle fingerprint 5a3551872679c8d463fbc99fc62a44c114dc009e32ad4fa8dc6cec98b0d252d8.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 5bd28d2d8bde46c01291ad149bec97f70ba311a729265bdb74e7386df0b8fc25.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 5c11f8efd9933e863b76679935b5dd348610ae46f3f2055668fa1f7b89d0c1f6.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, 0, -2, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 16 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2]

-- Cycle fingerprint 5c22158171dd7d3d9c59986f0681b9924400b9ac4fca0e4cb0c9682fee0c1aaa.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 7 0, .triangle 5 0, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 5c82a8bceae50980113a94d73f970773cdb7cb82e71eea911a6022bc6eb7d22d.
def localCycle00050 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, -1, -1, 3, -3, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 5e5e7d25421640fd0648d9782e416023cec58b1ec93be69b868f5ac63ebee77c.
def localCycle00051 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 1 3, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 5ecc2dc6cecc17ddae3d8225b5783760859ead5cac38511958ee54e1214c089f.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 5f7e2dd48bba0c9ce311dd97964b0f6d6c419a194c5bc7825738b77d91409739.
def localCycle00053 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .corridorLower 1 3]

-- Cycle fingerprint 61153bffe186b3ec1b0fff0c8e4aa3fdb2a35723c9fc1d8320bd60a6d5f87970.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 642a0776d26fad31693c43110174c89348c6c37cfd8bb64f3ec7230921ed09f1.
def localCycle00055 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 66a48a08245837dddf39b326cd36967745b7e5c5e3b19e2afff0c0a3525109e1.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 18 2, .gapLower 1 3, .corridorLower 1 3]

-- Cycle fingerprint 67509b28614860e8ddcae85e70fb352caa73f7e853632355efa5731be8a30703.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 6812f0cb6e6c1a39ac0e4f4f360ac2e68cd22e96432a260c42324029654d0897.
def localCycle00058 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 68149d5b3ec9f39230dfc67d72c054d71c1f4b0af9ebd57f0ed3a794f347d133.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 1 5, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1]

-- Cycle fingerprint 688126b7087bafdfed600a76f33265b813c1ccfed3f137c0d99521bb5aa2a309.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, -1, 0, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 2, .triangle 19 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 6a6dd224e5e57bd25311159dae41fba01c0393800fc1c9b477043f9e2fea6ec9.
def localCycle00061 : Cycle where
  length := 16
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, 0, -1, 0, -1, 3, 0, 0, -1, 0, -1, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 21 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 6b8cdbed6b0c35c99e49827566ce663d2b0ec00741e71b3951b9a05a4852af2d.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 23 0, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint 6d424bb0fee793b3b1187cf5df0a4f72bb7f4bfca93fe29009b4a3fd08a1bad4.
def localCycle00063 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 6e0bad29262823278e2247145b3f9d7a58daacd5987987abce0454cf6007b29d.
def localCycle00064 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3]
    constant := ![-1, -1, -2, 3, -2, 0, -1, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false, true, false] }
  origin := ![.triangle 11 0, .triangle 21 0, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 17 1, .triangle 18 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0]

-- Cycle fingerprint 6f662579af694e8ce58e466036df049f6fe0fac470b2dbb27cb55d3f95d6859b.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .gapUpper 5 2, .triangle 10 1]

-- Cycle fingerprint 6fdccbe3b11bb85ac2380a1d2a1a82367480590c5d2ccd5c5963281b9dffc693.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 7245ab967423989c0ce613f7fd0b987eac6989bf562a4cffa2bbb170323e2bc3.
def localCycle00067 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![0, -1, -1, -1, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 7 1, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint 7259d913abf72cf39e13ef91f091ddc0e73ba3cfbd4c0a36d2bd31fc9ebc02a4.
def localCycle00068 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 72f671879cd58837a5216ce40d74ef1ca1f66308e8dc35a14bcb7ba0fc06f1ef.
def localCycle00069 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 73bcd225a092d29be6619b2991fd633b79cc2330c5763eddfd66375b56beb66c.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, false] }
  origin := ![.triangle 25 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 16 0]

-- Cycle fingerprint 75f03291c9206094fe5e56195548f7ff90f5ffc1453d272ca0b651f0723f22bb.
def localCycle00071 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 4, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 768cd24c1446f4e247f4c4717e1a8a7a1088a86a7d056c604a0ef77f83cbe0f3.
def localCycle00072 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 76f0618dd7b5f23fa84fe0b6bf70f66ff509313eb5062b8ec1fc07344e0ae663.
def localCycle00073 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-1, 0, -1, -1, 2, -2, -1, -1, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 8 0, .triangle 27 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0]

-- Cycle fingerprint 7708aa451a5e258f272339d4dfeb8124171cc9fa44c38ba3c07f1a6df6dd5c84.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6]
    constant := ![0, 0, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 18 2, .triangle 23 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 0]

-- Cycle fingerprint 77bb6618699b53b95d6fb8848a7d7aabd3882944554b6f817a79c48ced80ca6d.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, 0, -1, 0, 2, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 3 0, .triangle 24 2, .gapLower 1 3]

-- Cycle fingerprint 77f4bc0cb88c089fbc931c085889b437e0841d1017585b42aa9285ead55c318f.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 10 0, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint 7851a6ccf253ccf981e799dad1623cca08d9f9a5da734b26d4f6a38cf161ff67.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 7d16f12f40c41fa3a7b06d47771a59717e5cb8723778621511c7e604a756354d.
def localCycle00078 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 17 1, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 7d753d5af4f3ffdde45231988a78999324af0730c044b7707c2d5a67bba5b1d2.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0]

-- Cycle fingerprint 7e209c2563946a7d822350c23123fd2a3ccd31f5408e5afe08445903579347d9.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 8169b727e266f442ac804b920b0e2e016d8257d81afa7ad8f30f05cdd58d591b.
def localCycle00081 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 8190cd75e209a4c53eb5b56c706b5c2954d5c56f0a892cce6bf8ef52ca70623b.
def localCycle00082 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-1, 0, -1, -1, -1, 0, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0]

-- Cycle fingerprint 8553b601074bc69fe6906aa30291c8b1eae3b43a44b035dbf5d3b95fcf02d2cc.
def localCycle00083 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .corridorLower 1 2]

-- Cycle fingerprint 868b1be11ca825773aad590bac731f0c50a009a720dfbf38214da68ed262ca12.
def localCycle00084 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint 87e1c721c80e02647b1c419022ca72d30762bf7c155dd2ff4f361e20b83f6d84.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 8ac4aa43cd7f557a1a174236de144fc6fc3a4ee01a8c9ee84bfbed6c1cb229a5.
def localCycle00086 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 17 1, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 8c1db926167aa90d0b1e8f320f4fbd564431eaeed664494af541ee9fa4102d46.
def localCycle00087 : Cycle where
  length := 15
  data := {
    node := ![.theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 0, 3, 0, 0, -1, 0, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8cd2e38d486a1dd160e03bcc6f4e89fc194f2bbdcd49012c175f629e66c83b70.
def localCycle00088 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .triangle 18 2, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint 8d1bc83adf72700082ba0463469afd405f567ad4b6d958fb8da7ba4b8b62f75b.
def localCycle00089 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.triangle 5 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 2, .triangle 7 1]

-- Cycle fingerprint 8d2cbec0a92616dc9cb242e41c4737577f0a4432c2895d91ea45109c82d09cbb.
def localCycle00090 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 90af1fe1cf6e09bd4501f3571b490ef97f5c853b653e1de610d4e3050c8dc3a0.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .gapLower 3 0]

-- Cycle fingerprint 923e85425ecbd39e1c1a186377f08321557b3466388ae6931666efb0bcc1033d.
def localCycle00092 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 9878ccae0c6e6412246969461f0e724968656a9c6f86ff5587d21cad14783da3.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .gapLower 3 0]

-- Cycle fingerprint 993566884aa9c7c7fb0aa6ecb02bbafa2baedc0641867912472b403fadb6b45c.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, -1, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 9bb84f8118c12f0668f50e3fbd3c6b3c6c9e87023e816d2ba167d3849e91614c.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-1, -1, -2, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 5 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0]

-- Cycle fingerprint 9e15d0008cc04a81d3b956e8acfe1aeb53d341077ccd71fdbde8bab21b84a1b3.
def localCycle00096 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 9ee7ba87c20d2a144444685ea8377a436fe11ea73d3f765c00fff154ced6d2ad.
def localCycle00097 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, -1, 0, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 9f3ec60a32ba1fe399778468409629e658bcde32ae7a41c96cd7e2e42d436bcc.
def localCycle00098 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 30 1, .gapUpper 5 1, .triangle 17 1, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint 9fcf3a307ef00747dedb2472cacb0c68f284d6326be7bf7721c83f3d62993c56.
def localCycle00099 : Cycle where
  length := 15
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2]
    constant := ![-1, 0, -1, 3, 0, 0, -1, 0, 0, -1, -1, -2, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, true, false, false, false, false, false, true] }
  origin := ![.triangle 18 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .triangle 11 1, .triangle 9 0, .triangle 19 0, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 9fe323ca1883962b51c32988bb1d5b97938103d2ca2e302422e1526f25b28f1b.
def localCycle00100 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 2]

-- Cycle fingerprint a1064165122209d043081849081fca199132aa6f05c93db4ce8c21f0d41f4469.
def localCycle00101 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint a1c13d43838e00f5248516d8c18475adba13888cb5569a9b26e683a1c2f8ff9a.
def localCycle00102 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint a43928e75db7093f70e6dd99b11a3f681b3633cda6fbc196eb40febbca8cec34.
def localCycle00103 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint a6d9320ee112865d74b4d0f8648d7e9046d644100b9e7afbdff5956d6879c998.
def localCycle00104 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint a6eb1ad6fcf2c5777966a42ad35c99e0d63689ccf0327727f90a6f4888f097df.
def localCycle00105 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint aa2f45fa45e32081ff4d9eae73aa74feba89faa15d53efb61e216151039e52ae.
def localCycle00106 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3]
    constant := ![0, -1, 0, 0, 3, -1, -1, -1, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .triangle 19 0]

-- Cycle fingerprint aac01e152b36645ef9aa5bad575cac169fe6abf59d629c4678be5e7326d7b4fa.
def localCycle00107 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint aaefa1d81acbe182ada6e3d47e32d34e205e3d784c9b8bd7d0309c535fee7350.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint ab685b21a0dd83eb3dca28f048f4317a23d094e2005a389756e1ad12cb439945.
def localCycle00109 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint ac3edf17d34fc39601fc288a8cb9558a2650aaca48b7f565f454bdf747d0b2fb.
def localCycle00110 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint ad01a70a45d8e01a87ef3dcf4da70ec0508eb902d4aa2ccc95a027ec9e50a030.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4]

-- Cycle fingerprint b11a720c8fff208a1b729778ab172fb7328f5110c9faeb3a697094c0bfeb2564.
def localCycle00112 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint b1c244979d65a643d8b71657aa0105095b58ae9c5dc4a592f53ada4694abbb96.
def localCycle00113 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 4, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint b3c4ccccf8acf4783b32f39a12de2a418e1e4960d2d65d3e1a5846b76f45687f.
def localCycle00114 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, 0, 0, -1, -1, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 7 0, .triangle 8 2, .triangle 11 1, .triangle 9 0, .triangle 19 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint b3f7c423336e0c514a02a5586d466d044ee2a7b6283422937809b453992c5eb3.
def localCycle00115 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 16 0, .triangle 29 0, .triangle 34 1, .gapUpper 5 1, .triangle 17 1]

-- Cycle fingerprint b494585c15fa3b0c9a6e18a300ae83fad2370415d325401b354b5ff4c793c017.
def localCycle00116 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint b5b646243293e66f56ba5831b715de236e89fe912104231fe1a3498351a65604.
def localCycle00117 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 4, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint b6605a5ed6799aa1ba51591dcfd7a79cb1e4eeaf10ea9c60bad459b0359a00f7.
def localCycle00118 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint b78ff471fbad278a423bb9ed41751b5910fe787bb38253a064c256c03ff2698e.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 6]
    constant := ![0, -1, -1, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true] }
  origin := ![.triangle 11 1, .triangle 9 0, .triangle 19 0, .gapLower 1 0, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 2]

-- Cycle fingerprint b9b6a4bb29c81500c5d3d2ddb58c9fa88360b2318796b4e35f8238b908dbbf1b.
def localCycle00120 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint b9e71b8a0b933f0a7fb41c37b368bcca263ced1dfee6394bfac604d615bf8e25.
def localCycle00121 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -1, 0, 0, -2, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint ba1f4a80f558c4a698d7e586e50f1a0d85062f7363f78d9c6bce3336db2d028d.
def localCycle00122 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 1, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint ba74ae9d2245aa768910a70ffd70fefd51bbf74c82c34613d62dc7c1eb6b6e50.
def localCycle00123 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint bb2a1bae2c844d1c05a43da727f98421c6bb830575512760d1ff6a71ea5b08e3.
def localCycle00124 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint bb826f1c90bd907b272dc58d82c4e613cb7f7ee7647270e1adec3703568cf851.
def localCycle00125 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 3 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint bd874e4dc5ee5404484eee87afd8d657d109b4eff279ac8fe89a3359b803dcc9.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 2 5]
    constant := ![-1, -1, -1, -1, 0, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 5 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 30 0]

-- Cycle fingerprint bdbcec24b7e17a2308259c9fd2d10307ce2802eeabb4de52332d7ea413e46b60.
def localCycle00127 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint bef14d8102401c02962869dc12287d584e9cce566855490c9fdc88e644e5d021.
def localCycle00128 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint bfe7de5bac737680c32ac9219670a04efba55ad1958574f76bd2faaaf6f5808c.
def localCycle00129 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint c102d817aa48ee14ca314a07b5792f495c341003f460ad6e7b37360154ec9206.
def localCycle00130 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![-2, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint c20cd5042a007a149b4ad8c18a8133a1adabf00b84df3a4e26e9dfcac4be69ef.
def localCycle00131 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .triangle 11 1, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint c26545d52cf01cf6591962c8fec1eef561b679df0a193cb08db3790a88974c19.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint c5330cef256da1420dc35df4ed26408a5f7c438d95bedb787e81104af4cb3716.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3]
    constant := ![-1, 0, -1, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 11 0, .triangle 32 1, .triangle 19 0, .corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 5 2]

-- Cycle fingerprint c7949ab6c0203cb8d27f13c92c2655a3c8816d3052da86d5f6b75f8f8cdd4c43.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3]
    constant := ![-1, 0, -1, -1, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 11 0, .triangle 32 1, .triangle 19 0, .corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 5 2]

-- Cycle fingerprint c8e67d5848b9915b629a49ad24c9fb3d8df12f3823c5abc195f15157a97d8773.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint c8ed3426ae54ba2a072581917b70d75edb48dfe6eb89c47892a4238aff3799b0.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3]
    constant := ![-1, -3, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0]

-- Cycle fingerprint c9183f2bdb6ce6c9c7fb5d226cd84a7be886a70df2d43a4f000330fb901772fc.
def localCycle00137 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 2, .gapLower 1 1, .gapUpper 2 1]

-- Cycle fingerprint c9af448dae04e1dc5b93bb5e08937338d3d1de5fbd07ddb43d076a55cb0fa8d3.
def localCycle00138 : Cycle where
  length := 14
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, 0, -1, 0, -1, 0, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint c9e6e6c018a70b292e39d1d49efeabe8b0a568e7ae64f4d1b2d31837532abc4d.
def localCycle00139 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, -1, -2, 3, -2, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 0, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint cac395a6fd1adbd7aebc2ebb4bec05a0ddc9ad32d80e308eb272916ebeaeda3b.
def localCycle00140 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![0, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 7 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint cc2da55a47742a61ab8caadc104a6848d5c0f4a1cdc7a53151158a11262bf58e.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Cycle fingerprint ce1e21cb66a1df70310111d9363d02f048445a8555391781b8ded11efa4c7d1f.
def localCycle00142 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d099f799c23f84c81d9d1d9c166ab393218734c1e2befb1d2d20aa855e58a87b.
def localCycle00143 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .triangle 25 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d0d0ccea72cba74e1ce89deac78173e261080c5f259d57c0c130718cb9073143.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3]
    constant := ![-1, 0, -1, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 11 0, .triangle 32 1, .triangle 19 0, .gapLower 1 0, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 5 2]

-- Cycle fingerprint d4f75b344d55ed4edb895ca91a8a4d1db561a3066b433b7e101295b037210a30.
def localCycle00145 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint d56dca3803b7a2cebc13cb07cc856be407b8c33eac6ef6ecbf0ece5ac2804fc1.
def localCycle00146 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 3 5, .distance 2 5]
    constant := ![-1, -1, -1, 0, -1, 0, 0, -1, 0, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .gapLower 3 6, .gapLower 5 4]

-- Cycle fingerprint d664a03529e5679178bab3d3dd39869bebc2ca8e92b59612644087f372785dcb.
def localCycle00147 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint d6912cb93637e0fba44d492d1489d92ce2f902828df5928e1ca9ddd5cbc7206d.
def localCycle00148 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3]

-- Cycle fingerprint d6956c4d50a7e20bb812798bc9c32a97d8edded57708ae3b8aba4ca8b28b3fcc.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint d6b9cc655c9eb21f0f6baf1dc3111a2929d6e4fe9ca7ebee8caad2e60b0552d3.
def localCycle00150 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 19 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint d732d3e9fce23aa1a758066d73c1ce5e7120d82708b6dc34bcf79b6428ac745d.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint d7792dd349dd16aa81fdb61382276b8e53483ba2e5fdbdfef9beed0e04aa3588.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 4, .theta 3, .distance 3 5]
    constant := ![0, -1, -1, 0, -3, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 5 4, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .gapLower 3 6]

-- Cycle fingerprint d8daa5827e82f48327884e0caf37340ea564c69e730dcfb21abc2df8c831d04b.
def localCycle00153 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint dd90aab19fcd513343f19ad2d1e43b4c7fe2dc0cfb9a3ced08d5b520883ced22.
def localCycle00154 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint dd982935e24ac7e5fd03bcbb1ae230bd3410caaae28232689ab088a3486584cd.
def localCycle00155 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint e0376e979095cf2e3dadfa1ba1fd5300bc6da6641601e0e0b6133b444ff9d6c1.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-1, 2, 0, 0, 0, -1, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 5 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 1 1]

-- Cycle fingerprint e1a8c616942c057b97b3e8d7efa0fa35f305851cc8e4dc79401a8eec6eded215.
def localCycle00157 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint e202a305708949c9102deac926d3052410d27e4f1ba4ae798f433da20c231485.
def localCycle00158 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint e2821b87234f6285aba941b165cd2ea85e08bf493d4e8ffcf3c48b8212123592.
def localCycle00159 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint e36e4110d2f5b3fd1290b1713e419533ec1adfdfa0f96592716664b55f64c0e8.
def localCycle00160 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint e3c83c85719cc221e381d04fc10f0a7a44b7f7e8380b347f257dd9b252ada3a8.
def localCycle00161 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint e40ae0c84a705b3ea219c3432df57438f0b27f12ccfa25a999241eaa9fa78e01.
def localCycle00162 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint e50252eb41399d6e4a5228646a3f87479e59ecc2ac6aecdc0952ddb08ff07658.
def localCycle00163 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, -1, -1, 3, -3, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint e9f3cec7b74174dc94b116a4ae16b89f64384c93a32d7741b2a01cf8e2a9f615.
def localCycle00164 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint eaa3cb8f11df8fc02f9f27e5f7e341bb9509eef623e1abbcba1c87e9c9a6bbb2.
def localCycle00165 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3]
    constant := ![0, 0, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 15 2, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 5 0]

-- Cycle fingerprint eeee96fefc7a5a07c1eec495fb6ae74e4e85fbfdb3d13397790f18ea3b7f3bac.
def localCycle00166 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint eeff608101a72b956ab1b890ef0226f141a7ec02d35b30d53b616dfd02d9ee85.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 3]
    constant := ![-1, 0, -2, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 9 0, .triangle 19 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 5 2]

-- Cycle fingerprint ef11d6ca655b58622a9042fa256490f81eeeb39cd04e7ab9b209a186414caa4b.
def localCycle00168 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint f14e62acce30a47073f8851a8fe936b673f196d9f5a08ef33cfff7c2a7459dd1.
def localCycle00169 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint f2f38056591695cec68d4270895cca051dfa5dc9e7160c874d8999281ba712e2.
def localCycle00170 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint f36c4977cbd1a1fd49924a9175b2d6825ba8ac02aa726b1447ddbda8f705d185.
def localCycle00171 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 2, .gapLower 1 1, .gapUpper 3 2]

-- Cycle fingerprint f3fe3065cb95345efaf93f6ab129e0e8c6df4ec1003f258c14246f7f05e0bc10.
def localCycle00172 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint f5b20f82ff330af31d24916ce8131e612c71d0956682a3f3cdeee0247b34792a.
def localCycle00173 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![0, -1, -1, -1, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 7 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint f5dbda3907a88ed8ce7cbc43a1032e523bb14241b5cfce7db91d9aa676a4299f.
def localCycle00174 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 24 0, .triangle 20 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint f67aeeaa80304f9238ec27d3bc565b84b7e767c5aebe5209bdd1e802cdacafa4.
def localCycle00175 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 2, .triangle 21 0, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint f8724b931d5b3d4cd051648df909d73fedfae8b494e74ec6fb4f44b49a067614.
def localCycle00176 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 18 0, .triangle 30 1, .gapUpper 5 1]

-- Cycle fingerprint f8c473328f9940fd0f58c9a5a6598db586b8d9b387a05372e44db1c6256730de.
def localCycle00177 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 19 0, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint f90a2a9ef7adb571edb5af4331d6f73ca0ad0b2574aad62fabf23fdd624fc324.
def localCycle00178 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint f9b90ea5f736c702a2e86b2b7c34ced22e25c172521781f9e0c92dccb3b84b61.
def localCycle00179 : Cycle where
  length := 10
  data := {
    node := ![.distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6]
    constant := ![-1, 3, 0, -1, -1, -1, -2, 3, -2, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0]

-- Cycle fingerprint f9c48f215a7adcc838c174bc329ebe5513b9de6c95cf4a2532362a3b12f4f68b.
def localCycle00180 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint fa2ae0ffadb2773d0e4003fcfb52a810b28ba33804dbeccd9eb47a69c431e36b.
def localCycle00181 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint fa397ec14157f67cc20f6774733063c3f33b66462dda9ded3663c5527ba2ca86.
def localCycle00182 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint fcaf484772f86922e2c4d4260c6d7843e3a3ace1a48770766f990b19fa50dc38.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 2, .triangle 19 0, .gapLower 4 0]

-- Cycle fingerprint fd1105a12996e07d38b22694cbffd50e53f80ca07176f674442d09cfa9e77689.
def localCycle00184 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, 0, -1, -1, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint fd3ba523112913f3a2c25a755f61b80b1e557224fc91d84f7ee00a3dec6ce484.
def localCycle00185 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint fdc9138c1dc50a34bf20f0daedd4a326d21420e986129f1cadb067a713ab1cb4.
def localCycle00186 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![0, -1, -1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 7 1, .triangle 8 0, .triangle 18 0, .gapLower 1 0, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint fdf5f77ea5ef057086d2c0e7ff31a1d7f0b1e7d46e8c91de65daaf619eb7db98.
def localCycle00187 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .theta 1]
    constant := ![2, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 5 0, .triangle 15 2, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint feb834128d3a9b7ff7c7e6497e2aa45a78ef4d7001748bd80fe25e42ee64aa77.
def localCycle00188 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .gapLower 4 0]

-- Cycle fingerprint ff6a146d9f66c53d1e03155621e07c57d2e97f271daf87a5f786104468f61bf4.
def localCycle00189 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .gapLower 3 0]

-- Cycle fingerprint ff6b9e641ec3d972ca8ed646017f4a574bbaca234c3098d8e2be32439c14e118.
def localCycle00190 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 4, .theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 4, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 19 0, .corridorLower 3 4, .gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3]

def library : Library := fun id => if id < 95 then (if id < 47 then (if id < 23 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 17 then (if id < 14 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))) else (if id < 20 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)))))) else (if id < 35 then (if id < 29 then (if id < 26 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)))) else (if id < 32 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none))) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))))) else (if id < 41 then (if id < 38 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)))) else (if id < 44 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))))))) else (if id < 71 then (if id < 59 then (if id < 53 then (if id < 50 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))) else (if id < 56 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))))) else (if id < 65 then (if id < 62 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)))) else (if id < 68 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))))) else (if id < 83 then (if id < 77 then (if id < 74 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)))) else (if id < 80 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))))) else (if id < 89 then (if id < 86 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)))) else (if id < 92 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))))))) else (if id < 143 then (if id < 119 then (if id < 107 then (if id < 101 then (if id < 98 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)))) else (if id < 104 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))))) else (if id < 113 then (if id < 110 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none))) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)))) else (if id < 116 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)))))) else (if id < 131 then (if id < 125 then (if id < 122 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)))) else (if id < 128 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none))) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))))) else (if id < 137 then (if id < 134 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))) else (if id < 140 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none))))))) else (if id < 167 then (if id < 155 then (if id < 149 then (if id < 146 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)))) else (if id < 152 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))))) else (if id < 161 then (if id < 158 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)))) else (if id < 164 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)))))) else (if id < 179 then (if id < 173 then (if id < 170 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)))) else (if id < 176 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none))) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none))))) else (if id < 185 then (if id < 182 then (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none))) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)))) else (if id < 188 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none))) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![4, 3, 6, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 102 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21120)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 4, 6, 0, 5], ![1, 2, 3, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 154 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21121)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 4, 6, 0, 5], ![1, 2, 3, 6, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 80 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21122)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 6, 4, 0, 5], ![1, 2, 6, 3, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 142 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21123)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 47 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21124)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 65 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21125)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 3, 6, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 102 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21126)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 4, 6, 0, 5], ![1, 2, 3, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 154 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21127)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 4, 6, 0, 5], ![1, 2, 3, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 80 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21128)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 6, 4, 0, 5], ![1, 2, 6, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 142 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21129)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 47 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21130)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 178 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21131)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 150 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21132)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 178 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21133)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 0, 5], ![6, 1, 2, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 27 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21134)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 4, 0, 5], ![6, 1, 2, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 58 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21135)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 0, 5, 6], ![1, 4, 2, 0, 5, 6], ![1, 3, 2, 0, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 126 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21136)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 0, 5, 6], ![1, 4, 2, 0, 5, 6], ![1, 3, 2, 0, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 106 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21137)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 0, 5, 6], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 111 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21138)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 0, 6, 5], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 184 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21139)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 0, 6, 5], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 42 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21140)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 3, 0, 6, 5], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 42 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21141)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![4, 3, 6, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 6, 0, 5], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 34 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21142)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 6, 0, 5], ![1, 4, 2, 6, 0, 5], ![1, 3, 2, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 143 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21143)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 3, 0, 5], ![1, 4, 6, 2, 0, 5], ![1, 3, 2, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 97 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21144)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 6, 0, 5], ![1, 4, 2, 6, 0, 5], ![1, 3, 2, 6, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 182 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21145)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 3, 0, 5], ![1, 4, 6, 2, 0, 5], ![1, 3, 2, 6, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 166 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21146)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 3, 0, 5], ![1, 4, 6, 2, 0, 5], ![1, 3, 6, 2, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 82 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21147)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 3, 0, 5], ![1, 6, 4, 2, 0, 5], ![1, 6, 3, 2, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 89 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21148)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![4, 3, 6, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 3, 6, 0, 5], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 34 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21149)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 3, 6, 0, 5], ![1, 4, 2, 6, 0, 5], ![1, 3, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 143 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21150)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 3, 0, 5], ![1, 4, 6, 2, 0, 5], ![1, 3, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 97 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21151)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 3, 6, 0, 5], ![1, 4, 2, 6, 0, 5], ![1, 3, 2, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 182 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21152)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 3, 0, 5], ![1, 4, 6, 2, 0, 5], ![1, 3, 2, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 166 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21153)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 3, 0, 5], ![1, 4, 6, 2, 0, 5], ![1, 3, 6, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 82 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21154)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 3, 0, 5], ![1, 6, 4, 2, 0, 5], ![1, 6, 3, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 135 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21155)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 4, 3, 0, 5], ![1, 6, 4, 2, 0, 5], ![6, 1, 3, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 135 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21156)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 4, 3, 0, 5], ![6, 1, 4, 2, 0, 5], ![6, 1, 3, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 159 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21157)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 4, 3, 0, 5], ![6, 1, 4, 2, 0, 5], ![6, 1, 3, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 159 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21158)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 0, 5, 6], ![4, 1, 2, 0, 5, 6], ![3, 1, 2, 0, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 77 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21159)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 0, 5, 6], ![4, 1, 2, 0, 5, 6], ![3, 1, 2, 0, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 183 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21160)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 0, 5, 6], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 8 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21161)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 127 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21162)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 94 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21163)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low (![136, 137, 122, 53, 68, 163, 173, 60, 28, 95, 95, 139, 32, 63, 130, 120, 124, 165, 71, 158, 81, 187, 55, 100, 140, 185, 116, 38]) }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21164)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![4, 3, 6, 2, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 6, 0, 5], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 174 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21165)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 6, 0, 5], ![4, 1, 2, 6, 0, 5], ![3, 1, 2, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 87 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21166)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 1, 2, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 190 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21167)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 6, 0, 5], ![4, 1, 2, 6, 0, 5], ![3, 1, 2, 6, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 2 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21168)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 1, 2, 6, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 190 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21169)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 6, 4, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 1, 6, 2, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 103 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21170)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![4, 3, 6, 2, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 3, 6, 0, 5], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .low (![25, 137, 122, 152, 68, 50, 67, 16, 121, 51, 20, 3, 186, 10, 5, 90, 161, 74, 5, 125, 81, 21, 30, 4, 56, 185, 116, 73]) }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21171)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 3, 6, 0, 5], ![4, 1, 2, 6, 0, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 164 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21172)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 54 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21173)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 175 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21174)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 3, 6, 0, 5], ![4, 1, 2, 6, 0, 5], ![3, 1, 2, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 169 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21175)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 1, 2, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 54 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21176)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 6, 4, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 1, 6, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 52 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21177)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 1, 2, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 175 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21178)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 6, 4, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 1, 6, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 66 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21179)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 6, 1, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 69 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21180)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 3, 0, 5], ![6, 4, 1, 2, 0, 5], ![6, 3, 1, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 118 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21181)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 6, 1, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 40 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21182)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 3, 0, 5], ![6, 4, 1, 2, 0, 5], ![6, 3, 1, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 101 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21183)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 0, 5, 6], ![4, 1, 2, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 145 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21184)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 0, 5, 6], ![4, 1, 2, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 188 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21185)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 0, 5, 6], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 57 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21186)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 172 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21187)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 92 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21188)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 92 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21189)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![4, 3, 6, 2, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 6, 0, 5], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 155 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21190)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 6, 0, 5], ![4, 1, 2, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 108 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21191)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 2, 1, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 146 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21192)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 6, 0, 5], ![4, 1, 2, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 112 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21193)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 2, 1, 6, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 146 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21194)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![4, 3, 6, 2, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 3, 6, 0, 5], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 155 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21195)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 3, 6, 0, 5], ![4, 1, 2, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 108 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21196)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 24 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21197)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 155 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21198)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 26 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21199)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 3, 6, 0, 5], ![4, 1, 2, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 112 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21200)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 24 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21201)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 22 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21202)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 26 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21203)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![6, 4, 2, 3, 5, 0], ![4, 6, 1, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 2, 6, 1, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 49 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21204)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 6, 2, 1, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 189 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21205)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 3, 0, 5], ![6, 4, 1, 2, 0, 5], ![6, 3, 2, 1, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 168 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21206)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 4, 0, 5, 6], ![1, 2, 3, 0, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 170 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21207)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 4, 0, 5, 6], ![1, 2, 3, 0, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 141 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21208)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 91 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21209)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 153 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21210)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 46 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21211)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 46 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21212)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![4, 3, 6, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 131 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21213)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 4, 6, 0, 5], ![1, 2, 3, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 157 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21214)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 4, 6, 0, 5], ![1, 2, 3, 6, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 39 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21215)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 6, 4, 0, 5], ![1, 2, 6, 3, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 129 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21216)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 138 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21217)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![4, 3, 6, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 131 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21218)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 4, 6, 0, 5], ![1, 2, 3, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 157 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21219)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 4, 6, 0, 5], ![1, 2, 3, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 39 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21220)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 6, 4, 0, 5], ![1, 2, 6, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 129 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21221)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 148 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21222)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 150 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21223)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 1, 6, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 37 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21224)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 6, 1, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 76 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21225)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 4, 0, 5], ![6, 2, 1, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 149 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21226)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 4, 0, 5, 6], ![2, 1, 3, 0, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 107 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21227)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 4, 0, 5, 6], ![2, 1, 3, 0, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 177 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21228)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 4, 0, 6, 5], ![2, 1, 3, 0, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 93 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21229)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 4, 0, 6, 5], ![2, 1, 3, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 13 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21230)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 4, 0, 6, 5], ![2, 1, 3, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 151 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21231)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 4, 0, 6, 5], ![2, 1, 3, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low (![132, 171, 117, 83, 68, 59, 15, 45, 160, 160, 160, 179, 11, 180, 48, 43, 105, 167, 113, 72, 128, 86, 23, 70, 75, 185, 116, 7]) }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21232)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![4, 3, 6, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 4, 0, 6, 5], ![2, 1, 3, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 110 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21233)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 36 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21234)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 6, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 104 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21235)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 6, 4, 0, 5], ![2, 1, 6, 3, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 96 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21236)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![4, 3, 6, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 4, 0, 6, 5], ![2, 1, 3, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 110 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21237)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![4, 3, 6, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 4, 0, 6, 5], ![2, 1, 3, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .low (![114, 171, 88, 162, 176, 12, 29, 41, 18, 18, 35, 99, 119, 0, 98, 35, 78, 44, 98, 35, 33, 1, 35, 17, 9, 35, 35, 6]) }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21238)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 123 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21239)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![4, 6, 3, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 1, 3, 0, 4]], proof := .low (![14, 171, 79, 162, 176, 12, 134, 147, 181, 84, 35, 64, 144, 61, 98, 35, 78, 156, 98, 35, 33, 133, 35, 17, 9, 35, 35, 6]) }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21240)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 109 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21241)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 6, 4, 0, 5], ![2, 1, 6, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 31 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21242)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 1, 3, 4, 0]], proof := .tail 19 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21243)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 4, 0, 5], ![2, 1, 6, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 1, 4, 3, 0]], proof := .tail 62 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21244)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 4, 0, 5], ![2, 6, 1, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 85 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21245)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 0, 5], ![2, 1, 6, 4, 0, 5], ![6, 2, 1, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 115 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21246)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 4, 3, 2, 5, 1], ![6, 3, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 6, 1, 4, 0, 5], ![2, 6, 1, 3, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 76 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21247)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (21120 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 21120 ≤ id.val) (hhigh : id.val < 21248) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 21120)) = true := by
  let j : Fin 128 := ⟨id.val - 21120, by omega⟩
  have hsum : 21120 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (21120 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard165
