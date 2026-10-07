import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard170
open N4R2OuterLeftReplay

-- Cycle fingerprint 01b8161dc4b1abe809710e6976b3e795e8f7ebe577bc09c3f837661fbd0e91ff.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 02c079ee4401fc18aa09e27cc427f8da46fb222ab0bd3532cb0cbf462c509b84.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 6]
    constant := ![0, -2, -2, -1, 4, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 23 2]

-- Cycle fingerprint 05881fead65314bc00b199fb30de9217d0ba2e5435f428a35bfd3194652958c1.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 6, .distance 0 4]
    constant := ![-1, -1, -2, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 8 2, .triangle 13 1]

-- Cycle fingerprint 06a1a5730659e288bcedd76566d17b5e7c9c5d112aeafd8b5a0890d693cf36b1.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5]
    constant := ![-1, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0]

-- Cycle fingerprint 08a6f0dec5832b7ad36c447e936a613c04e754dccf2634ef5176b7daaf14cc91.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6]
    constant := ![0, -2, 0, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 6 2, .gapLower 1 3, .triangle 20 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0]

-- Cycle fingerprint 098283bdb3a291b41344460a4c4b62681032d0b87b8769e7ce2914e4c3802e9e.
def localCycle00005 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 0c4bd127dc1f6bace1a99811295dc00e2a6540b8a036c9a03bae4d8d1387d03a.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .gapLower 6 2, .gapLower 1 3, .gapLower 1 2, .triangle 16 1, .gapLower 4 0]

-- Cycle fingerprint 0e01dfd5d54f432167a9f7682855302e486c6f4803c642bad10b353baf5aa68a.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 34 1, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 0f755c488b9b52a2a2724075d1b5be06a36166525769c741a10384cbbf7d0576.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 10fd0d24aac9f150cbb2a642fbbc1e97b24d61182cc4531c5a51656a0675bb60.
def localCycle00009 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Cycle fingerprint 141077b780ca89bffd337505eb1a8eec56343ae2dc13bc29ef1d079f668479d0.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 149e9cedecc5456d4756d8355314522cf45116fafc5323c56e256e42956e9900.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![0, -3, -1, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint 14cdc4b5ecd9b7bc8bde2520255170c8df2f950787be1473fcc66c74582ed8d6.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint 1546a9a38150f9a763cda117ff804c922898917a226ba06532d6037d68eb6bb6.
def localCycle00013 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Cycle fingerprint 16aa92ff2eccda2f4be003a6d3645044cd346f68cc0aad6fb6c3176e9133d353.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 176cba4c581ee537f6e85a71c9ec5fc0ceaaffec1fe7b225865f237af994261a.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 6, .distance 0 4]
    constant := ![-1, -1, 0, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 8 2, .triangle 13 1]

-- Cycle fingerprint 1d271ed5f7d262f604c7ba0c165e7c794a13fe3087d987c138cc4335444ff42e.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 2, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint 1e0fba968eb3f581d803e37a77272334935e9e2be5ef9ac01273f7ec22a866b5.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 1edcc6716266b043e29f421551cd687da65f282d9c36ce5b109e0ea72a0be602.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 1f0ce2152b7d2950319e87a12b2f6c9dae308da32b95a370d933b3ee0a62e952.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .gapLower 4 0]

-- Cycle fingerprint 1f398f5ff7aa99a534039397ad03ab9a9a86b6be300eb45c2a1efb7625aeaa94.
def localCycle00020 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, 0, -1, 0, 0, -1, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 2214d6178e1d6e890d9d0e1849945c06a3e1a76384250f205424e978630ec30f.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 265eb377495eaf03ee722dc6eabd9d9a344dc113c5aa13d9375b857252bca4de.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0]

-- Cycle fingerprint 2726d84c4d5ed16878fb88492a964d1ec33b5c17f1da8b1b9340c7a7b1dcfddc.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 2a35085220e11876569dca1e438105fa8177d8024f96c0c037b5f80b4b5cfdcd.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint 2b6a881a62be3c8fdd3bcbb5581a8e1d7f6df6755d32634825dae019d688b37b.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 23 2, .gapLower 1 3, .triangle 20 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 2bf49deaec89edf0b3aa7803e59e213aefdfdbc06ace4df1ef4bec6af2c9d262.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5]
    constant := ![-1, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0]

-- Cycle fingerprint 2e3c75cfc75b0aa35a54f21f91e98a10ee2c7beb889ad2539d512fc3ced3bd20.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 2fcfcc87cce986f59eed78d4e7032540685e1645c590bff0bfba401fb907cbfc.
def localCycle00028 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 31e110071854a5bf9b5013ef895226ed45351f7676028e3902b64ba706b840cf.
def localCycle00029 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4]
    constant := ![-1, 0, -1, 0, 0, -1, -1, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 0]

-- Cycle fingerprint 32379c26458a1f4df12240e422370c75f556a0b90a0eefc555a409fe422148ef.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, -2, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint 34b38c647af1f606732b61bd2980b71ca0d85642187818f01194576764b5a94b.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -2, 3, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 38167058942c07b5786a7fd46e0acadaf374bbc42dcd4d1ef2251cf6aca6cee8.
def localCycle00032 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3]

-- Cycle fingerprint 387ad890bcc1e2441cc48e6bde0f5c70f40497df531cee9f9b6dac8e88088c99.
def localCycle00033 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 18 2]

-- Cycle fingerprint 38c5af3c3f4daeec4fb97a32ed86cc85cb38dd826c2f0ff8561e6be5f8b6412d.
def localCycle00034 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 0 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 3a8dc3de71e72d398432fc7156c462e2b586b959d35b4f0b2a5aa8e0d7f04241.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-1, 2, 0, 0, -1, 0, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 3be8b98006f307a2993e23d537f03d2000bbc497ac5990a1f1e6c214031196a8.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 3ce6c5b7dc7e7a82d37bf2950b1e23a64a0d84ce936146b5bf9cd86c5aa360d0.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 17 0, .triangle 30 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 3e49bc5ecc7e8c2b4510229a8fba95293135b4f7fbbf8fc695e03bbcf1770bb3.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 3e4f2dbbd2b41b0878d76d6ca23d63c2a42b3896db399b5e52439564bcaf2a7c.
def localCycle00039 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 0 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 3ee6da7469e1ce9f3de176e27793d5914bf42732788d2b45816c01d6668e6b93.
def localCycle00040 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6]
    constant := ![-2, 0, -2, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 0, .triangle 18 2]

-- Cycle fingerprint 3f23149319ba31764b7ee3c1709421e5086db41ea184e660be848577bfabaf62.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 406e46057281b83401227086671cfcd2f822080884fc934bd627bfb99d4d651d.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 3 6, .theta 6, .theta 5]
    constant := ![0, 3, -1, -1, -1, 0, 0, 2, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, -1, 0]
    strict := ![true, false, false, false, false, true, true, true, true, true] }
  origin := ![.thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .gapUpper 3 3, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 40f0cfc9aeb9c0240bab5c94384e51ee88c22cf58e61f5248086ebc47006e01e.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .gapLower 4 0]

-- Cycle fingerprint 41229be201a7cbe7b283b31714022fc69d30fc3ad127c3531286de376087b125.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 412e9b6453c86cdbacaf640656710bdcc754d1b34b2bd8c9a756b7e13cc13ab1.
def localCycle00045 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![-1, 4, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 5, .gapLower 1 6, .triangle 0 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 420a43629e5d2ec85132bfb7f9360e7afb9c2674da09e81733cd4a0f026ab466.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6]
    constant := ![0, -1, 0, -2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 34 1, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 13 0]

-- Cycle fingerprint 431805120aaa78af61e4bd3f066b32dc5fb376e0a6d9543a4d7cf38e3a443ddc.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6]
    constant := ![0, -2, 0, -2, -1, 4, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 13 0]

-- Cycle fingerprint 48a38cea03088bce8e4a676c395257c991e7bc84d50a6b32df5ad578be61cb7f.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 4ac9f288fe21d82ed2707daf60d6da0feb89479872ad804878346bba708631a6.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4]
    constant := ![0, -1, -1, 0, 3, 0, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 22 0]

-- Cycle fingerprint 4cb03708c4eb4361cd2e7af3a2b6b830823ffd4b17940806ef58ab6357e0436c.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 7 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint 4d89bed07a72fb14790cc023207e0a8502016736fe276548398a44549b2a4128.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint 4ff6a16d45514493aca067770898ed9149874c39fbd0dcd6fb33d79f103e4229.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .gapLower 6 2, .gapLower 1 3, .triangle 17 1, .triangle 28 1, .gapLower 4 0]

-- Cycle fingerprint 51779dbf6767dc52e432c6eb1db6b861f8d84a9a8fa81e9254fd42119a9d2b3c.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 7 2, .triangle 14 0]

-- Cycle fingerprint 51aa8df933669732802503bb955181e95fa6deebe680683b563354bf77c5ca4a.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 6]
    constant := ![0, -2, 0, -2, 3, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 23 2]

-- Cycle fingerprint 5288aef4b81e7604bb3cc0860c5afb1c536630538dfa2cc868a7cf286e8e1c62.
def localCycle00055 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .gapLower 1 3, .corridorLower 1 5]

-- Cycle fingerprint 54116481b4a62d5a85cf4e434d948d2ca6fd3e430d9b3d208a248da0f8a49b40.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 544d860f9e2f9d10e6d3c414dcfef6e777a34eeb3d2699a1e6a81f10263e9a64.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6]
    constant := ![0, -1, 0, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 34 1, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 13 0]

-- Cycle fingerprint 55189e6fae4d486cbd1ce4cf90e327948a8478dc668dc7c0a740d7319c7bf165.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint 5727576f3054d95c5692b476222709dc86208105d0b91a9a36704cdb1b8e40cd.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, -1, -1, -1, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint 57f2fc82a85fab0b27170f98d14960e07a2d0ae63537fe8acb66019fa2c3608d.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 29 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 5d020f2e20d52478c370c8bdbd857e9e32e2ee6d61aae179cb87333ee2c04bba.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint 5e0156005fa42c242ecd311f0a384ac534b79fa3b2a28ee3a4c9827d252f4e59.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 5f6bf37f160a2a1e37fe37f58d10aa15cd070b7609679a8691d467772e0d209d.
def localCycle00063 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 5fabdaff79ce44baeb1a5056b0737ceddc83c87d7ce621daccb7aa15f716ca39.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -2, -1, 3, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 62ee4fd0e2357ae0164f1289bf429e78ed9ced42fd657f6a3707e717039af412.
def localCycle00065 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 632582c1ab9de0d4257a7e9a549c4b4fc5eb80bf494eb57773245577d38cd41e.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 64aadc95bbdcc9d49a2f9fc92939a44feb8a21ad8df3ee1ef350d362939cbcf0.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 6, .distance 0 4]
    constant := ![-1, -1, 0, -1, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 8 2, .triangle 13 1]

-- Cycle fingerprint 65522f6aaca4421877f83cccf960080880b45e0a1be24e0252d848811257dfbd.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 23 2, .triangle 24 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Cycle fingerprint 66418fa9293373ee06089a3027c038efef1d1ba6e599557b0eb1b955803e1cb9.
def localCycle00069 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 2, .gapLower 1 3, .gapUpper 5 2]

-- Cycle fingerprint 669e82fb07930c2264668479cda1968ec51db202fef594d3cf4aab43236b007b.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 22 0, .gapLower 1 3, .triangle 18 0, .triangle 27 1, .corridorLower 2 3]

-- Cycle fingerprint 66b3bb19ec76d7fb6d9c86ccc110e3afd4b6ca60bf79b0886a44ef73df2311d3.
def localCycle00071 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, -1, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 691d2953ecda808414733d88744a59a4b43c44d2cc8adfd7165fcf5b9f822008.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 6a69a3dfbaaaffddf1850f0b3b0aed9ef81e93780657bd1fd222ce9f5730b442.
def localCycle00073 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 3, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.triangle 15 0, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 28 0, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint 6d3a843e8ae224d054b563443eb6f05075971c2c15f0c6c2687412a2102f2801.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 6ddb1aec40902caae77dc35d95256998f8432b03df495440c16a41065f217902.
def localCycle00075 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint 6e62fb4dfb6e1f17fa80d22806eab8e9fd97075886abfa7b7329f4c598b4d8a8.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1]

-- Cycle fingerprint 7068f413f044da0f8e88bad35d02e0b5c56c3e40bb46316e730d6b260fa0ef7b.
def localCycle00077 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 718edcc0ac864cbb1b79a0371b6de5e02aefff6badb8c86b779a3345e110180d.
def localCycle00078 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 2]

-- Cycle fingerprint 72c43a48eee05f1d6e70055b124b7c05018b62f256c17c3ae53c50e8e4a787d5.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6]
    constant := ![0, -1, 0, -1, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 34 1, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 13 0]

-- Cycle fingerprint 730060e99e944ab942c6a2582cb3b5b49c2478d76c5dddaf1b8fd743a8013d03.
def localCycle00080 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 2, .gapLower 1 2, .gapUpper 4 2]

-- Cycle fingerprint 73c0941116fb26eae331413f068e5d468c97f2a2f874c27465fca0c6e2b3dfdc.
def localCycle00081 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![0, 0, -1, 0, -1, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 76aea7610f6b3e4332a56f242970f71809bae720ceb3715152151a64ca9fb901.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 2 4, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 16 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint 7b04923cfeb143f87f86779243fb3d422729f2c73bc281c126abf73ea484d99a.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 7b8110436b3a26b61ac7c48b515b59deccea0212cc0a34525d0b383e82b99dab.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 30 0, .triangle 17 0, .corridorLower 1 2]

-- Cycle fingerprint 7d5a15b128831f0156bdfa4c05fb00e068db91a42be8c8eeef20554ff27df403.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![0, -1, 3, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint 805e3d4fed5c00228dc44752c960b5b2b5c8d1e167848dddf2d61c9f1c3efb07.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![0, -1, 0, -1, -3, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, true] }
  origin := ![.triangle 6 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 80fa4bbe870ae77ffaf1b4a035573b282bd287492dec9ac5ac27361573a96949.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 6, .distance 0 4]
    constant := ![-1, -1, 0, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 0 2, .triangle 8 2, .triangle 13 1]

-- Cycle fingerprint 81bb6b5a1b7e193c269ecb45922ee4efe8345f6f62f545bc80868cf2dae571f9.
def localCycle00088 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 4, .corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 8558652c00cd5a349a4196d04e21b17a0bf26deea0c755c41a89f882f644f877.
def localCycle00089 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 18 2]

-- Cycle fingerprint 85e921865b38bb5f91552851603bc1beab65a4a32caa9156c9f326126ef2e886.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 86bef04538bb77a1fcd2dc42b2226703e9269b3a876a8a89aa4047fd85954e1b.
def localCycle00091 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 87b8ab8e23dbb40d33dad7cf1a70e83c35ea40b4e69199eef3734a5a825efc9c.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 88548f4a2098daa407c9b6939e916e6608cea2a496747014f1b2e3bd74a024ff.
def localCycle00093 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![2, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 7 2, .triangle 14 0, .triangle 24 2, .gapLower 1 3, .corridorLower 1 5]

-- Cycle fingerprint 8d768a78bd22b677186b6bc247128e9e690c7615843bbd6cede69dc18922696d.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 16 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 8e3352de33df87d122891748ef8eb33d09332fd6bb9fda3e3e1512c9e27b464f.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 8ebccc06953ff9cec6659351ff8ae3508c41aa28386f8b3e9d1363d23259863d.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![-1, -1, -1, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 9317f33eccce2ee1d3d0fa5af481a93efc1000a8ddf82e6bda54ad926954f5df.
def localCycle00097 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 9720d51845fc57f5d7a7787510be542508c17245b90c6e84234b1dff2f55e875.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 3, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.triangle 15 0, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint 984cefe5aece596eb6807d83c9f29ab025cdba5a46a52ae2fde6971f40c0c2db.
def localCycle00099 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 98887a5c70278cc221b59c8468f6d65abb997d04c586fd5332c2c645cf9b2b6c.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 9acf7d495e2dff520d7f1f6df0226fcc6d8b98202b13055ea7bde7075bd8f9c5.
def localCycle00101 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 9b483b9b503cf83dd66ef6dcff615b8a4685d4408196495ffbd54f76b0e35620.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .distance 2 5]
    constant := ![0, 0, -1, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, false, true] }
  origin := ![.triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 18 0, .triangle 30 1]

-- Cycle fingerprint 9c27be26c3aee9e38590261465c7be84f768f4b05921edc1d5f363741127f43f.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, 0, -2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .gapLower 1 6, .triangle 0 2, .triangle 7 2, .triangle 14 0]

-- Cycle fingerprint 9ce9904a2d175bf695b2aee7c917220b4e622400390af067aae6de01a35969a7.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 9e885665a98cbfcfe7a45c2fd56e22013c14e834ae31bf4e6da3b855a32a5a5f.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 9f3c9374a3a2ab3237b5aac598aaa9c5806df3f39c24fe4150865518620c9a57.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint a0258e379fdcec3c2166d0e2f673e449b75b1485538c194b9a838993d476a83a.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4]
    constant := ![-1, 0, -1, 0, -3, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 6 2]

-- Cycle fingerprint a38819f0fc1df88be80f743664663fd7de17e423078da19dbca8ed6f799ee120.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5]
    constant := ![-1, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0]

-- Cycle fingerprint a98af0ffe2231721cbf3f283d1e4ab7d71ae0a7615d5423242b5929315deaf3b.
def localCycle00109 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint aa856c0543042324699a712e99fb5b689f80cb8b6265dd90971fd8734375f46e.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 2, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint ab8fda7ae0a777a2ca61162179802454eb0d1024036da5ade8a086eb741d4d9a.
def localCycle00111 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint ac88cb734ac1ce388b5329f2a581f58bf8cb89e425c4867fc5bdf892f8387a69.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 23 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6]

-- Cycle fingerprint ad426ce369eda9eaeecddec358836666f5a95473d23352d8b7f0439b7c77c43d.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 5, .distance 1 4, .distance 2 4, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .gapLower 1 2, .triangle 16 1, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint ae5ba559792cdd4cdf014710e3d95e8b2537b012022abc6069ccd024fdeca4d8.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 5]
    constant := ![-1, 0, -1, -1, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 28 0]

-- Cycle fingerprint af21e610fab5ad0528c0902eda7bb40a35b9920cae0938a2f862e08864f72617.
def localCycle00115 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![0, -1, 0, -1, -1, 0, -1, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint b49441016c99690bbd819a68a4e59ebed351559e5e8e53e2cb11fa912993bf88.
def localCycle00116 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint b5e60ca95c5f43accfcc524bc2a9a8320948f392ab721b6fb852718f8ec45cd1.
def localCycle00117 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint b68c812350459daed21a0e156ea8cd906679aae876b1d9898d127af759388707.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![0, -1, 0, -1, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, true] }
  origin := ![.triangle 6 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint b9f8e4fb86a4f9f4f3ab595afa72b91e433033817f9b94c735b1e50110125c36.
def localCycle00119 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint bb6b7bad9b830a21912af9a31cd90d83ed9f20044d034281c189794b3ccc3099.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint c20afa46adda53d651a813d5b31a977c00b61628f6cdd838418c1d01e9f7ccfb.
def localCycle00121 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint c339faf8fa9e5cc5331aba09ee5edd2e25bca23eac2470aedbd20a7503ca006f.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint c409a66816a643c9aebd7fffa58e43cbed169176252b41b9f5196bd9fd30faac.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 6]
    constant := ![-3, -1, 3, 0, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 23 2]

-- Cycle fingerprint c5505b78adda8b9160b29ee4ab38aa6943535276c89ad90a2587b4951ed6dcc3.
def localCycle00124 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, -1, -1, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0]

-- Cycle fingerprint c77382e405014ef2ce24e6a9300a7b84181db96089509cd15566cfb3365ed09b.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 2 4, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![-2, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 16 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint c7b2ce5a4cf32baec7838b2cb5752235a913bf0da1024fadab40a149d25bec86.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint c8417777c678bc4c5c3bdb1ad2bb9dec311a163036ed936edf5346b33d6ca0ba.
def localCycle00127 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .theta 2, .theta 1]
    constant := ![1, 0, -2, 0]
    coefficient := ![1, 0, -1, 0]
    strict := ![false, true, true, true] }
  origin := ![.gapLower 1 6, .triangle 0 2, .gapUpper 2 6, .thetaNext 1]

-- Cycle fingerprint cae60272a428908ac95c0fa0fe47a3e8327f1e53e38ce95903c76b5bb79dba2f.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5]
    constant := ![-1, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0]

-- Cycle fingerprint cc01618ec81c418b4fb325c67dea8fb3d58393dafc913a691bbb9f93a71116b4.
def localCycle00129 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![2, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 7 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint d05ed29845d51e63ee55d08d20e66ba9f8eb197bb04db0363e38fb7cdb15e3a3.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint d2c136ed5150bc1bee2e32c05a1b023f589b156c5f360e15fbed24de2f4a77a5.
def localCycle00131 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 30 1, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint d478c16fc634028ff146fa698df94500238373e679378857aceb358f77c1186a.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 23 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1]

-- Cycle fingerprint d6ac22001ce2bf7f557663db8a90cab97a55f1870fb0da8c274884d7f7e4152c.
def localCycle00133 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint d7d92ad480aad038b8d1db6a6e23a7f4506765a349f48faf6049f7f94b643e6b.
def localCycle00134 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint da72de67f4a1885449a88de93dd0f7d6f05794ebc36cc6ad611561dab19dae75.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-1, 0, 0, 3, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint db6f4b6b31b82fe5ac95264b4077b85d5f5b20d9da6901c355797a6a8388131c.
def localCycle00136 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint e362a11c0715b21ddd975e93d8661e25b45d4f27b128a5cba26b525769a39fb5.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 1 4, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 16 1, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint e49ccd498e68c878ed66e5c93f66504d00513db0f4071c0784951be1f7ba2e83.
def localCycle00138 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint e8de99ac7c53b7b753861348c54f5dd34cbc347f337debd9050fb836a00769ff.
def localCycle00139 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint e9a7900efc50aac46b3f2bdf60c0dc3bd8089c058beb44bfcb2ecab53101ae80.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint ebb2703533b3e03debdaf7e8d84073bc642368239b4287b4c8e0a81d717cac9d.
def localCycle00141 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 34 1, .triangle 28 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint eda87d4d41405a694e2f7ed904df993df34543a7e729cc7bdcaef796a031a2a0.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2, .distance 0 6, .distance 0 4]
    constant := ![-1, 0, -2, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 2, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 0 2, .triangle 8 2, .triangle 13 1]

-- Cycle fingerprint ef5cc329968cb31a8b3a27da4b97fb7365b1ce26199dc19f9f3e0f940f03867d.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint f04014145d905766bbb1e0b813fb450af970d732df79d6418a6aaf021e57e06c.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6]
    constant := ![0, -1, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 34 1, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 13 0]

-- Cycle fingerprint f0c0bf2b7cf4c6d62b153318350a722df2aac2d7ff7b8b5a46086a525355c3d4.
def localCycle00145 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint f1bdfd48a6a416b2fc83270bf55f4a1f4f4a2b23eaf68536198e52aedc4a3ea3.
def localCycle00146 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint f31b1a1fcdc15751576c139f6cb492d36ef4849b026cfc13a0f6e2102fee55e3.
def localCycle00147 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint f4700d2b0f6aa7cab64d79187ac9c663c5e6630b9feaf41d309bd7293247a1e5.
def localCycle00148 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint f78daa45720f06038b6545b4f05c063c43e2f93bbd54c85f1ae3ea572cb6cb16.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, -3, 0, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint f85ad52ea39f251a1788d0b273a5df23a4d804346d0893cd16932e84757274cc.
def localCycle00150 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, 0, -1, -1, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 23 1, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint fa777600f32738a13551444d13fb884f9e6cf6ecf2151b9d0fe46370a3892e0c.
def localCycle00151 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2]
    constant := ![-1, 0, -1, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, false] }
  origin := ![.triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 3]

-- Cycle fingerprint fad4fdcfc46409b79730fc62e970bf255518b79fe4d2239d777562c8e59ad154.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6]
    constant := ![-1, -2, 0, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0]

-- Cycle fingerprint fd1765b84b05080c54f2b98d2786c45e0c3f5e99db98a863402eb0c8b59fe09d.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint fd6bae91ce05bcbfa3661d7e8fadd1ee63d478da13e1a17ad2a3e0298be623e4.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint fdb6859184878d7120cf2a326ccca592c863f03ac7251971ce50976fab494b6d.
def localCycle00155 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 5, .corridorUpper 0 1, .triangle 0 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint fe1abd58d6da47f1ca78f27fe7cc6470506f4b827aebbad26677d2c04b661fa1.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .triangle 23 1, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

def library : Library := fun id => if id < 78 then (if id < 39 then (if id < 19 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 14 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)))) else (if id < 16 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))))) else (if id < 29 then (if id < 24 then (if id < 21 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))))) else (if id < 34 then (if id < 31 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))))) else (if id < 58 then (if id < 48 then (if id < 43 then (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))))) else (if id < 53 then (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))) else (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))))) else (if id < 68 then (if id < 63 then (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))) else (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))))) else (if id < 73 then (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))))))) else (if id < 117 then (if id < 97 then (if id < 87 then (if id < 82 then (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))))) else (if id < 92 then (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))) else (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))))) else (if id < 107 then (if id < 102 then (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)))) else (if id < 104 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))))) else (if id < 112 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))) else (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))))))) else (if id < 137 then (if id < 127 then (if id < 122 then (if id < 119 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)))) else (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))))) else (if id < 132 then (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)))) else (if id < 134 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))))) else (if id < 147 then (if id < 142 then (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)))) else (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none))))) else (if id < 152 then (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)))) else (if id < 154 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![3, 4, 5, 6, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![2, 1, 0, 6, 4, 3], ![2, 1, 0, 5, 4, 3]], proof := .tail 42 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21760)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![3, 4, 6, 5, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![2, 1, 6, 0, 4, 3], ![2, 1, 5, 0, 4, 3]], proof := .low (![149, 11, 82, 69, 63, 78, 50, 30, 152, 4, 39, 124, 103, 125, 52, 145, 59, 53, 6, 109, 125, 129, 45, 89, 93, 75, 5, 102]) }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21761)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![3, 4, 6, 5, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![2, 6, 1, 0, 4, 3], ![2, 5, 1, 0, 4, 3]], proof := .tail 153 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21762)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![3, 4, 6, 5, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 2, 1, 0, 4, 3], ![5, 2, 1, 0, 4, 3]], proof := .tail 37 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21763)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![2, 1, 6, 0, 4, 3], ![2, 1, 5, 4, 0, 3]], proof := .tail 13 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21764)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![2, 6, 1, 0, 4, 3], ![2, 5, 1, 4, 0, 3]], proof := .tail 68 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21765)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 2, 1, 0, 4, 3], ![5, 2, 1, 4, 0, 3]], proof := .tail 13 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21766)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 6, 1, 0, 5, 3], ![2, 6, 1, 0, 4, 3], ![2, 5, 4, 1, 0, 3]], proof := .tail 13 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21767)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 2, 1, 0, 4, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 13 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21768)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 6, 4, 5, 1, 0], ![2, 1, 0, 6, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 2, 1, 0, 4, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 91 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21769)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 0, 5, 4, 6], ![1, 2, 5, 0, 3, 6], ![1, 2, 4, 0, 3, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 44 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21770)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 0, 5, 4, 6], ![1, 5, 2, 0, 3, 6], ![1, 4, 2, 0, 3, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 73 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21771)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 0, 5, 4, 6], ![5, 1, 2, 0, 3, 6], ![4, 1, 2, 0, 3, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 17 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21772)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 4, 6, 0], ![2, 1, 0, 5, 4, 6], ![5, 1, 2, 0, 3, 6], ![4, 2, 1, 0, 3, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 120 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21773)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 0, 5, 4, 6], ![2, 1, 5, 0, 3, 6], ![1, 2, 4, 0, 3, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 136 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21774)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 0, 5, 4, 6], ![2, 1, 5, 0, 3, 6], ![2, 1, 4, 0, 3, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 154 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21775)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 0, 5, 4, 6], ![2, 5, 1, 0, 3, 6], ![2, 4, 1, 0, 3, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 97 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21776)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 1, 0, 5, 4, 6], ![5, 2, 1, 0, 3, 6], ![4, 2, 1, 0, 3, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 74 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21777)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 5, 4, 6], ![2, 1, 5, 0, 3, 6], ![2, 1, 4, 0, 3, 6], ![2, 1, 0, 3, 4, 5]], proof := .low (![22, 108, 80, 55, 63, 78, 67, 26, 16, 116, 39, 10, 87, 135, 40, 145, 58, 2, 88, 109, 33, 142, 155, 89, 15, 75, 5, 102]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21778)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 5, 4, 6], ![2, 5, 1, 0, 3, 6], ![2, 4, 1, 0, 3, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 156 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21779)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 0, 5, 4, 6], ![5, 2, 1, 0, 3, 6], ![4, 2, 1, 0, 3, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 56 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21780)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 0, 5, 6, 4], ![1, 2, 5, 0, 6, 3], ![1, 2, 4, 0, 3, 6], ![1, 2, 0, 4, 3, 5]], proof := .tail 99 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21781)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 0, 5, 6, 4], ![1, 5, 2, 0, 6, 3], ![1, 4, 2, 0, 3, 6], ![1, 2, 0, 4, 3, 5]], proof := .tail 73 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21782)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 0, 5, 6, 4], ![5, 1, 2, 0, 6, 3], ![4, 1, 2, 0, 3, 6], ![1, 2, 0, 4, 3, 5]], proof := .tail 38 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21783)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 4, 6, 0], ![2, 1, 0, 5, 6, 4], ![5, 1, 2, 0, 6, 3], ![4, 2, 1, 0, 3, 6], ![1, 2, 0, 4, 3, 5]], proof := .tail 120 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21784)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 0, 5, 6, 4], ![2, 1, 5, 0, 6, 3], ![1, 2, 4, 0, 3, 6], ![1, 2, 0, 4, 3, 5]], proof := .tail 43 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21785)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 0, 5, 6, 4], ![2, 1, 5, 0, 6, 3], ![2, 1, 4, 0, 3, 6], ![1, 2, 0, 4, 3, 5]], proof := .tail 96 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21786)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 0, 5, 6, 4], ![2, 5, 1, 0, 6, 3], ![2, 4, 1, 0, 3, 6], ![1, 2, 0, 4, 3, 5]], proof := .tail 97 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21787)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 1, 0, 5, 6, 4], ![5, 2, 1, 0, 6, 3], ![4, 2, 1, 0, 3, 6], ![1, 2, 0, 4, 3, 5]], proof := .tail 74 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21788)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 5, 6, 4], ![2, 1, 5, 0, 6, 3], ![2, 1, 4, 0, 3, 6], ![2, 1, 0, 4, 3, 5]], proof := .tail 96 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21789)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 5, 6, 4], ![2, 5, 1, 0, 6, 3], ![2, 4, 1, 0, 3, 6], ![2, 1, 0, 4, 3, 5]], proof := .tail 156 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21790)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 0, 5, 6, 4], ![5, 2, 1, 0, 6, 3], ![4, 2, 1, 0, 3, 6], ![2, 1, 0, 4, 3, 5]], proof := .tail 56 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21791)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 0, 6, 5, 4], ![1, 2, 5, 0, 6, 3], ![1, 2, 4, 0, 6, 3], ![1, 2, 0, 4, 5, 3]], proof := .tail 66 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21792)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 0, 6, 5, 4], ![1, 5, 2, 0, 6, 3], ![1, 4, 2, 0, 6, 3], ![1, 2, 0, 4, 5, 3]], proof := .tail 73 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21793)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 0, 6, 5, 4], ![5, 1, 2, 0, 6, 3], ![4, 1, 2, 0, 6, 3], ![1, 2, 0, 4, 5, 3]], proof := .tail 150 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21794)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 4, 6, 0], ![2, 1, 0, 6, 5, 4], ![5, 1, 2, 0, 6, 3], ![4, 2, 1, 0, 6, 3], ![1, 2, 0, 4, 5, 3]], proof := .tail 27 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21795)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 5, 0, 6, 3], ![1, 2, 4, 0, 6, 3], ![1, 2, 0, 4, 5, 3]], proof := .tail 19 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21796)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 5, 0, 6, 3], ![2, 1, 4, 0, 6, 3], ![1, 2, 0, 4, 5, 3]], proof := .tail 24 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21797)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 0, 6, 5, 4], ![2, 5, 1, 0, 6, 3], ![2, 4, 1, 0, 6, 3], ![1, 2, 0, 4, 5, 3]], proof := .tail 97 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21798)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 1, 0, 6, 5, 4], ![5, 2, 1, 0, 6, 3], ![4, 2, 1, 0, 6, 3], ![1, 2, 0, 4, 5, 3]], proof := .tail 18 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21799)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 5, 0, 6, 3], ![2, 1, 4, 0, 6, 3], ![2, 1, 0, 4, 5, 3]], proof := .tail 24 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21800)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 5, 1, 0, 6, 3], ![2, 4, 1, 0, 6, 3], ![2, 1, 0, 4, 5, 3]], proof := .tail 156 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21801)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![5, 2, 1, 0, 6, 3], ![4, 2, 1, 0, 6, 3], ![2, 1, 0, 4, 5, 3]], proof := .tail 137 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21802)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 0, 5, 6, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 0, 3, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 141 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21803)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 0, 5, 6, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 0, 3, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 104 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21804)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 0, 5, 6, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 0, 3, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 49 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21805)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 0, 5, 6, 4], ![2, 1, 5, 6, 0, 3], ![1, 2, 4, 0, 3, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 131 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21806)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 0, 5, 6, 4], ![5, 1, 2, 6, 0, 3], ![4, 1, 2, 0, 3, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 72 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21807)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 0, 5, 6, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 2, 0, 3, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 36 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21808)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 2, 0, 3, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 100 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21809)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 0, 5, 6, 4], ![2, 1, 5, 6, 0, 3], ![2, 1, 4, 0, 3, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 134 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21810)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 4, 6, 0], ![2, 1, 0, 5, 6, 4], ![5, 1, 2, 6, 0, 3], ![4, 2, 1, 0, 3, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 148 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21811)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 4, 0], ![2, 1, 0, 5, 6, 4], ![5, 1, 6, 2, 0, 3], ![4, 2, 1, 0, 3, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 151 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21812)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 0, 5, 6, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 1, 0, 3, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 133 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21813)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 1, 0, 5, 6, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 1, 0, 3, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 106 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21814)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 4, 0], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 1, 0, 3, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 143 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21815)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 5, 6, 4], ![2, 1, 5, 6, 0, 3], ![2, 1, 4, 0, 3, 6], ![2, 1, 4, 0, 3, 5]], proof := .low (![107, 86, 80, 123, 63, 78, 127, 118, 54, 25, 39, 31, 46, 1, 47, 145, 64, 144, 132, 109, 33, 35, 155, 89, 57, 75, 5, 7]) }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21816)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 5, 6, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 1, 0, 3, 6], ![2, 1, 4, 0, 3, 5]], proof := .tail 133 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21817)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 0, 5, 6, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 1, 0, 3, 6], ![2, 1, 4, 0, 3, 5]], proof := .tail 140 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21818)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 1, 0, 3, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 138 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21819)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 5, 6, 4], ![2, 5, 6, 1, 0, 3], ![2, 4, 1, 0, 3, 6], ![2, 4, 1, 0, 3, 5]], proof := .tail 8 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21820)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 0, 5, 6, 4], ![5, 2, 6, 1, 0, 3], ![4, 2, 1, 0, 3, 6], ![2, 4, 1, 0, 3, 5]], proof := .tail 14 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21821)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 5, 6, 4, 1, 0], ![2, 1, 0, 5, 6, 4], ![5, 6, 2, 1, 0, 3], ![4, 2, 1, 0, 3, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 130 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21822)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 0, 6, 5, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 0, 6, 3], ![1, 2, 4, 0, 5, 3]], proof := .tail 66 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21823)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 0, 6, 5, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 0, 6, 3], ![1, 2, 4, 0, 5, 3]], proof := .tail 104 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21824)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 0, 6, 3], ![1, 4, 2, 0, 5, 3]], proof := .tail 49 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21825)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 5, 6, 0, 3], ![1, 2, 4, 0, 6, 3], ![1, 2, 4, 0, 5, 3]], proof := .tail 41 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21826)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 0, 6, 5, 4], ![5, 1, 2, 6, 0, 3], ![4, 1, 2, 0, 6, 3], ![1, 2, 4, 0, 5, 3]], proof := .tail 72 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21827)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 2, 0, 6, 3], ![1, 4, 2, 0, 5, 3]], proof := .tail 100 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21828)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 2, 0, 6, 3], ![4, 1, 2, 0, 5, 3]], proof := .tail 100 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21829)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 5, 6, 0, 3], ![2, 1, 4, 0, 6, 3], ![1, 2, 4, 0, 5, 3]], proof := .tail 134 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21830)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 4, 6, 0], ![2, 1, 0, 6, 5, 4], ![5, 1, 2, 6, 0, 3], ![4, 2, 1, 0, 6, 3], ![1, 2, 4, 0, 5, 3]], proof := .tail 148 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21831)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 2, 0, 3], ![4, 2, 1, 0, 6, 3], ![1, 4, 2, 0, 5, 3]], proof := .tail 151 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21832)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 0, 6, 5, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 1, 0, 6, 3], ![1, 2, 4, 0, 5, 3]], proof := .tail 133 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21833)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 1, 0, 6, 5, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 1, 0, 6, 3], ![1, 2, 4, 0, 5, 3]], proof := .tail 18 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21834)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 1, 0, 6, 3], ![4, 1, 2, 0, 5, 3]], proof := .tail 143 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21835)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 5, 6, 0, 3], ![2, 1, 4, 0, 6, 3], ![2, 1, 4, 0, 5, 3]], proof := .low (![12, 3, 80, 123, 63, 78, 79, 128, 61, 25, 39, 126, 46, 113, 47, 145, 122, 144, 112, 34, 33, 35, 155, 89, 57, 75, 5, 102]) }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21836)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 1, 0, 6, 3], ![2, 1, 4, 0, 5, 3]], proof := .tail 133 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21837)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 1, 0, 6, 3], ![2, 1, 4, 0, 5, 3]], proof := .tail 28 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21838)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 1, 0, 6, 3], ![4, 2, 1, 0, 5, 3]], proof := .tail 138 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21839)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 5, 6, 1, 0, 3], ![2, 4, 1, 0, 6, 3], ![2, 4, 1, 0, 5, 3]], proof := .tail 8 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21840)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![5, 2, 6, 1, 0, 3], ![4, 2, 1, 0, 6, 3], ![2, 4, 1, 0, 5, 3]], proof := .tail 14 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21841)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 5, 6, 4, 1, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 2, 1, 0, 3], ![4, 2, 1, 0, 6, 3], ![4, 2, 1, 0, 5, 3]], proof := .tail 130 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21842)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 0, 6, 5, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 6, 0, 3], ![1, 2, 4, 5, 0, 3]], proof := .tail 139 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21843)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 0, 6, 5, 4], ![1, 2, 6, 5, 0, 3], ![1, 2, 6, 4, 0, 3], ![1, 2, 5, 4, 0, 3]], proof := .tail 51 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21844)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 0, 6, 5, 4], ![1, 2, 6, 5, 0, 3], ![1, 6, 2, 4, 0, 3], ![1, 5, 2, 4, 0, 3]], proof := .tail 90 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21845)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 0, 6, 5, 4], ![1, 6, 2, 5, 0, 3], ![1, 6, 2, 4, 0, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 29 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21846)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 0, 6, 5, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 6, 0, 3], ![1, 2, 4, 5, 0, 3]], proof := .tail 81 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21847)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 6, 0, 3], ![1, 4, 2, 5, 0, 3]], proof := .tail 65 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21848)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 6, 2, 0, 3], ![1, 4, 5, 2, 0, 3]], proof := .tail 146 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21849)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 0, 6, 5, 4], ![1, 6, 5, 2, 0, 3], ![1, 6, 4, 2, 0, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 71 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21850)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 0, 6, 5, 4], ![1, 2, 6, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 1, 2, 4, 0, 3]], proof := .tail 90 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21851)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 0, 6, 5, 4], ![1, 6, 2, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 117 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21852)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 0, 6, 5, 4], ![1, 6, 5, 2, 0, 3], ![6, 1, 4, 2, 0, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 114 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21853)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 0, 6, 5, 4], ![6, 1, 2, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 60 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21854)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 0, 6, 5, 4], ![6, 1, 5, 2, 0, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 101 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21855)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 0, 6, 5, 4], ![5, 1, 2, 6, 0, 3], ![4, 1, 2, 6, 0, 3], ![1, 2, 4, 5, 0, 3]], proof := .tail 65 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21856)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 2, 6, 0, 3], ![1, 4, 2, 5, 0, 3]], proof := .tail 65 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21857)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 6, 2, 0, 3], ![1, 4, 5, 2, 0, 3]], proof := .tail 20 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21858)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 2, 6, 0, 3], ![4, 1, 2, 5, 0, 3]], proof := .tail 65 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21859)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 2, 0, 3]], proof := .tail 98 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21860)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 2, 0, 3]], proof := .tail 62 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21861)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 2, 0, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 110 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21862)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 5, 0], ![2, 1, 0, 6, 5, 4], ![6, 1, 2, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 105 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21863)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 5, 4, 0], ![2, 1, 0, 6, 5, 4], ![6, 1, 5, 2, 0, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 70 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21864)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 32 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21865)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 4, 0], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 2, 0, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 92 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21866)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 4, 6, 0], ![2, 1, 0, 6, 5, 4], ![5, 1, 2, 6, 0, 3], ![4, 2, 1, 6, 0, 3], ![1, 2, 4, 5, 0, 3]], proof := .tail 77 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21867)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 2, 0, 3], ![4, 2, 1, 6, 0, 3], ![1, 4, 2, 5, 0, 3]], proof := .tail 151 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21868)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 1, 6, 0, 3], ![4, 1, 2, 5, 0, 3]], proof := .tail 143 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21869)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 1, 6, 0, 3], ![4, 2, 1, 5, 0, 3]], proof := .tail 138 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21870)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 5, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 6, 1, 0, 3], ![4, 2, 5, 1, 0, 3]], proof := .tail 95 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21871)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 4, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 48 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21872)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 4, 0], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 2, 0, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 121 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21873)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 5, 6, 0, 3], ![1, 2, 4, 6, 0, 3], ![1, 2, 4, 5, 0, 3]], proof := .tail 119 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21874)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 5, 0, 3], ![1, 2, 6, 4, 0, 3], ![1, 2, 5, 4, 0, 3]], proof := .tail 84 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21875)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 5, 0, 3], ![1, 6, 2, 4, 0, 3], ![1, 5, 2, 4, 0, 3]], proof := .tail 115 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21876)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 1, 2, 4, 0, 3]], proof := .tail 21 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21877)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 2, 1, 4, 0, 3]], proof := .tail 0 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21878)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 1, 0, 6, 5, 4], ![2, 6, 1, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 23 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21879)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 5, 0], ![2, 1, 0, 6, 5, 4], ![6, 2, 1, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 9 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21880)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 5, 6, 0, 3], ![2, 1, 4, 6, 0, 3], ![1, 2, 4, 5, 0, 3]], proof := .tail 85 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21881)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 5, 0, 3], ![2, 1, 6, 4, 0, 3], ![1, 2, 5, 4, 0, 3]], proof := .tail 111 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21882)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 0, 6, 5, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 1, 6, 0, 3], ![1, 2, 4, 5, 0, 3]], proof := .tail 147 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21883)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 1, 0, 6, 5, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 1, 6, 0, 3], ![1, 2, 4, 5, 0, 3]], proof := .tail 94 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21884)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 5, 6, 0, 3], ![2, 1, 4, 6, 0, 3], ![2, 1, 4, 5, 0, 3]], proof := .tail 85 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21885)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 5, 0, 3], ![2, 1, 6, 4, 0, 3], ![2, 1, 5, 4, 0, 3]], proof := .tail 76 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21886)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 5, 0, 3], ![2, 6, 1, 4, 0, 3], ![2, 5, 1, 4, 0, 3]], proof := .tail 83 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21887)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (21760 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 21760 ≤ id.val) (hhigh : id.val < 21888) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 21760)) = true := by
  let j : Fin 128 := ⟨id.val - 21760, by omega⟩
  have hsum : 21760 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (21760 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard170
