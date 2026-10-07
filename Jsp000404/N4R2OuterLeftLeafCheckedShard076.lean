import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard076
open N4R2OuterLeftReplay

-- Cycle fingerprint 01e780bfbcfffc87028ce6cb4b86308e04472734f5228e6c33f1d741e4b304fc.
def localCycle00000 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 24 1, .triangle 22 1, .gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 043d03fc192a3abef478c14ada843fc13719a4bc2a40692c7b68afa8274d98d1.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0554316a9e098cba7f6e23bb76fdf0b0c3050423c98359ffcf48cfca66a4b031.
def localCycle00002 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 058227b16efa5cdd331bdabfb26c8efa944fc9e5177da41642099444ea8fcedb.
def localCycle00003 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 4, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 22 0, .triangle 31 0, .triangle 32 2, .gapLower 3 0]

-- Cycle fingerprint 087b1ef9827d5816baea1971bb41bc7fbdb80b18c2480616bd0c5866f523b24a.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 2]
    constant := ![3, -2, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 1 0, .triangle 4 0, .triangle 24 1, .triangle 22 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2]

-- Cycle fingerprint 0b32adcb77fe5018cae5c28df98d1866823bbb8e061475a0bd0a86dc492d1d81.
def localCycle00005 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 0ef026da17f90eb5a0811ebe29058220d66bca501fce042fb18f570e335aa897.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 12 1, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 1510e304f5e6cf7c6411e3c84b140eb93989d4e96d11c7285f3c2abe66e7e532.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1, .distance 1 6]
    constant := ![0, 0, 0, 0, -1, 0, 3, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, false, true, false, true, false, false] }
  origin := ![.triangle 18 1, .triangle 27 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 159f587706115408d005da07139548684aed44a1c70e4147b9a026601ef701ff.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 1aae943d9ff2700c7b3a9c54a5e4fa89f26384af5e8eabd609027cd63d6189d6.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 0, .gapLower 2 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 1b207aae8d94103721b2923bfdb0e8c9d9cbf4d3d4f98ff2cf6ce5eb910fe457.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint 1bc8c54227af078ea49219659b7616723630e61cb3b46b3109c3ba2b23b665c2.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 2 0]

-- Cycle fingerprint 1cc979c7d260f87147863b21405958ced35650618e12b617611b8b655c7ca217.
def localCycle00012 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 204b88552a7ac0804fbbec2eabda5c29aef8864468e5b3c1cb64db03171adea2.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 209723164ead0564d7df252662791a42a8628afc12584b45b205b9a88e9290fd.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint 23b27d9c5faadb5a8dd08adccd6fd1e8d52a9b8a06b2c197fc27da181455c91c.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 298b19f06bb2696094d3b9a1d92e2fc59a7809a9cf5312a6c359d0b20e967818.
def localCycle00016 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .theta 1, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint 2f48125cf0b381bae316b98ed3ecb2b4897f2df46450a08ffc468147f8b98e49.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 30 0, .corridorLower 2 5]

-- Cycle fingerprint 336ade730320cb5516d83b785c8ec111a3aaf4bfc71d4702ba6db07fb4bdc909.
def localCycle00018 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 28 1, .triangle 16 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 372769c1fcb5e9ffeef5bf839569ddeddeba245eee1188605c5e5144fecb83a1.
def localCycle00019 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .theta 1, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-1, 4, -1, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 1 4, .gapLower 1 6, .triangle 0 0, .triangle 4 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 3a78bf31c49a1c0614d9be8593d47ce920d4dac34e3d7d35ca057aed2db293d1.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 4 0, .triangle 24 1, .triangle 22 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 3b450e9dad5c0bf5c8f5f92e7150f397024a9bb4052a38195164681170c0211a.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2]
    constant := ![-2, -1, -1, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 1 0, .triangle 4 0, .triangle 24 1, .gapLower 1 1, .corridorLower 1 4, .gapLower 1 6]

-- Cycle fingerprint 3ffd0c66c49c6d390f02d3ee4e7d3f3b3d8acd5a5380e399dcb616d25dfa8ef1.
def localCycle00022 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 24 1, .triangle 22 1, .corridorLower 1 4, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 442027de59d97e0863cdb9747e25c0be342143de35f57cebac1bd63af6c5fe43.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 461abf3aa8a2da5aa2cf791c3f326ef72425bc844ff793375f177e86976d16d0.
def localCycle00024 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 48f42332334ae1762443e71405be173c59d9d39541be529978cc10b738b7db94.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 23 0, .triangle 29 0, .gapLower 4 2, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4f62ac5034b8ebf62b177df8865cc209c961b25fe0ebacbbe25015ea14e7c2d0.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 6, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 28 0, .triangle 29 2, .gapLower 2 0]

-- Cycle fingerprint 5097e029df6eda0b468aa380dd389356c43d566e888929393e58d16c577a5da8.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 4 0, .triangle 24 1, .triangle 22 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 52e75df622ca15618b4b85e333d749c363bbd74018e611246977aaed871922b1.
def localCycle00028 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 54427107e42e5cf3a7cabe0cfd0924de04b52d8d293581a50f229abbbb324a9c.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 55e2c2e4838f9a2a8bca55821ab54cbbe1e5203f6876942b1e1d3e1c4409f81e.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint 57fa06ecd7a17e166e6974d12ef56a069c80d2a5a16e9aba145388c558581a80.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 28 0, .triangle 31 0, .triangle 32 2, .gapLower 3 0]

-- Cycle fingerprint 59a7f433115efb82c9f6a8d4e48bf47515cef799f75be97559c475186ac93444.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 59e235061381f14611a4bbe7060633742db474f9c338e1ec6d8c06fe89dfd534.
def localCycle00033 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 5bf05b20c02635766adea6b9361c3960c403764de253a9d8b71e6d6c8ffeb663.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5c547877a57e17b0dfa49e2a7e723c1f0035b42136a861cf10acc27d92ada2cb.
def localCycle00035 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 23 1, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 5cd0b88ee87c2e00d1f2c8a1c792c7c2ca4c969d114eb8f82ef1d98181c90c23.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 34 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint 5e459fb1e077ef422971606996d4d82cc7c22d1da1777f267013b4758830d885.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 6143897cb8a659adb7f86172dbdd273cb97cf26a03de08d4710ba60526041155.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 66659145a52e5784a8b18f08e3b90f358f96d92585070783b0524a8d6661eee4.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 718a6d04a176f04d74a82e1e1f0659ddba243a1c8301e9290bbd024e5b077456.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 756fb3be98d85d4494ca5e0db115923ae9f8c2016e0e6a9f25f5dcbdd54fb59b.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 0 1, .triangle 2 2, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 75e87fb2ab7c7c8b3b57b555a0b7101366c72a3df0486dc2caecbf10df96cfb3.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 21 1, .triangle 27 0, .gapLower 2 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 7ba93cb381efbfee3641ec258816275678d8b30f66ae088b9fd39c32095d6ce3.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![0, 0, 3, -1, -2, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .gapLower 1 3, .triangle 24 1, .triangle 22 1, .gapLower 1 0]

-- Cycle fingerprint 7fbcda6b1565d004219b3ce67238a1f0f0fd9ee7585f160bbfdf7734fef6d634.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![2, -2, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 1 0, .triangle 4 0, .triangle 24 1, .triangle 22 1, .corridorLower 1 4]

-- Cycle fingerprint 8066423995b203ac4cc760e2886eb543431609420053d0654f1ba6c7a1f8416e.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 823a53d0584967283478b2e0a8fcffa5d4ce11327c853037eb56375f0dbaef83.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![2, 0, -2, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 4 0, .triangle 24 1, .triangle 22 1, .corridorLower 1 4]

-- Cycle fingerprint 8547cf13e6c1c43cdc464ee83475bbf8c42cf59afb1cdee47f6821d0f7ba491c.
def localCycle00047 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 24 1, .gapLower 1 1, .corridorLower 1 4, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 85f4be4148ff88987eef94246bb1a99c434c23a212f537b91854682d4eda52bf.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 8c3ddfdd90a4f63a675c84087b191e9e66da920b023269f95e7b6e6383d73a27.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 8f0dcec04a6b5cf884eb2bdebe3f905f67d8fc38f6ba0af9aa64b46079d91129.
def localCycle00050 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 1 0, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .gapLower 3 0]

-- Cycle fingerprint 8f3a29d0808f0df047478676ca5cfbce4047760a56d2f0dfc6a676243a9c00f9.
def localCycle00051 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 0]

-- Cycle fingerprint 91a4df622d64cffa208433439dcef80c794f028d9c347cc4dbb5b265cfbde067.
def localCycle00052 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![4, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .triangle 4 0, .gapLower 1 2, .corridorLower 1 5]

-- Cycle fingerprint 9aa7201ea45feff2b8a17e947966d5d7566b43711580ccb5954dc8eac5dd98f6.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 2]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 24 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2]

-- Cycle fingerprint 9c6b26f3c2cf5b5063e0ba66e061c9ba9a13dfafd11703fe4f76629593c9ba50.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 9f0f754d32bf33b713b14fe8228f3d064ae824cc95b579e61a537b96133a88c8.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1, .distance 1 6]
    constant := ![-2, 0, 0, 0, -1, 0, 3, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint a138ad9353c9d556eb60e27dc8c325359c397695d1e3fe2ad2845d0a380be8a3.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a1c2d78425e7a250e8bb1e66f43d5fdf37c39be024584d29938565b28b2c4ed0.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1, .distance 1 6, .distance 2 6]
    constant := ![0, 0, -1, 3, -3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true] }
  origin := ![.triangle 30 1, .triangle 28 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 0, .triangle 4 0, .triangle 18 1]

-- Cycle fingerprint a4ab4e6b80e223b25f535394e75a1afcb4ec392c7adc3370fb4aa9fd23baa812.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint a54b782b9cf4a9956c12ef283798793e316bd0156e7d5585367707380e84707c.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint a6f75a053d4ee46de7ecf995e90f185eb92a0cd3756aed24e7e71ff3b286eb82.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a8710f5a02e1e63dff5a956481b566a66894a9657a06e3a1f484b5c49ca12b69.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 34 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint a87227d04f604e936f9f945bb39cbbd8b8369ab6462de01fc964a9e60d1e143c.
def localCycle00062 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 2, .triangle 12 0, .triangle 22 0, .corridorLower 1 4, .thetaLower 1]

-- Cycle fingerprint aba6d02d4c261ee6e3b1e63d16d4842f580d4612b990ecf166dfce8d047ad9b1.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 0, 0, -1, 0, 3, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint ad5cbe22d5c78e626a3ebc98d1aa98e4d22efd1b8f547e4247ceb5e3e90589ba.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1, .distance 1 6]
    constant := ![0, -2, 0, 0, -1, 0, 3, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, true, false, false] }
  origin := ![.triangle 24 1, .gapLower 1 1, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint b1143e7ac6be299616dce903ab4469eba81932ac200474ff8ddc03caba5e0b76.
def localCycle00065 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 22 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b114fc79d78d50018cb003f64386939c5b3c95d5c488677dd93fdf4744809896.
def localCycle00066 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 1 2, .triangle 22 1, .corridorLower 1 4, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint be2479d01730fc2c806f0d7ddd529fb8756e227c52589387fa8c1d45acc1f86d.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 28 1, .triangle 16 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .gapLower 3 0]

-- Cycle fingerprint c1ae5d452935485a8d50578fdb8b7a306c4ad240098c2756a6dbcc7584435f13.
def localCycle00068 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint c2e17bbd3483440f2814a84c446409b2ec74d8a6889353d98bac2688677e0601.
def localCycle00069 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .theta 1, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint c49dfdbdc37ed432659bd5c0c280b90f8ab6b929fc2ca348b03e48223313ba67.
def localCycle00070 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![4, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .triangle 4 0, .triangle 24 1, .gapLower 1 1, .corridorLower 1 4]

-- Cycle fingerprint c9406b519434ad0f102be1993d77eba029a8ecfc624e31006ecf8339c805a588.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint ccb1d9574993d1225bbabd1e6dfe414feac4cc21cbe0ff94d94515f1d342bc09.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint cd79947ff97dd572dd4abd4dcf14c5ef8dae83e7ae6435e6b943e4e8aa0aff8d.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint cda57d34d37b140a2371b6c1cf6f47b1aaa6052bc256341b53b691834af4578e.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![-1, -2, 0, -2, 0, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint d34c3d15375d228e5d84430aeebd85643bb69ed9aa961272474d9815de5a2be9.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 18 0, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint d5c12cf20efb02b50bcda3bf41ae9308d38c9a515c203d9805dae401d908ba8e.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .gapLower 3 0, .thetaNext 2]

-- Cycle fingerprint d605859564b869fb988904c1be332567bb94e9d54472890ef9cf7ff2c378c7c3.
def localCycle00077 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 21 1, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint d6ff75d09704ded2b3729580cf592123f11425348b83281713975a9cfe1eb7b5.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .gapLower 1 2, .triangle 22 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint daa8af5f20225b6074bf1b1001cdbf34b224ef450a107bf63d7f73739e795906.
def localCycle00079 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 4, .triangle 16 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint dab822866b4509b2f566cba62d2d7cfcb4895427f8b1b6f29b404ccc34737068.
def localCycle00080 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 22 0, .corridorLower 1 4, .thetaLower 1]

-- Cycle fingerprint dadf41238d665d803fe6f3c78cc11b472212be8835a7429298cea67a0a70a3ac.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 11 0, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e260d5fc10d94881ba36533961d51b3e22a2140e0574620831cf08f0c75c2ca2.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint e30697e520ead91ee16256224413f1a242a12fe73e69b65be298564666ab5241.
def localCycle00083 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 24 1, .triangle 22 1, .corridorLower 1 4, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint e514b48f658bd0192604136ccbc093c0fa42929cfb730d1f1e4bb627806d3571.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e8555b34e7380e3bc196ca2d33b53f6aa810f58a56aa15f9ea2771a8b7d05eb4.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint eb55c861f746129f74be0af4af5b0143687131ca6bfd6ab15cb67fd5c896fb49.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint ee65f295c37424e94eb12f03756aa075c64d326412392084f7f98271e4746293.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 6, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![-1, -2, -2, 0, 0, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 3, .gapLower 1 2, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint eedc8502273e1f2ac1c9515743617c126f3fc56b0d5f7d7f2b316921006b7137.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint f10848d0d028703f502b665fe72f150e1519ed6dfe2770578c257fce899a1d88.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint f15e573dab889e4d40b48b631e8152e1ea1ccf3b5b2690fc729629e0f3907433.
def localCycle00090 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 31 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint f363b0fb3dd13ca8a313e9c85d1b23b6067caa4b2366972ea25dea993ed9f2ac.
def localCycle00091 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 22 1, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint f46e390b5e04dd594595d5221381af339f014163d5c5a1c6790f1d971d5a702f.
def localCycle00092 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 5 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint f669573ba4aff27163d0011debae699158213bfeeaa772aa2610cd961987ce3b.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 5]
    constant := ![0, -1, 3, 0, -3, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, true] }
  origin := ![.triangle 28 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 4 0, .triangle 18 1, .triangle 30 1]

-- Cycle fingerprint f6ab68ffc41337b5d07464cf559d1ccd02675dc3158c05681d1c3f7c98dc0265.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint f731da76f191456a0f9d46bfbb1e86e4ba83d00f7a24eb712ccbb121fa029974.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint f749d5deb96a2d342924e49f6a066c3faab5b0f8180a46f0b80d8221b998f844.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint f9268c627256f1cdc0b50f26881cc273297f347427ec02138b1711d28cabdf0a.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint f936e6b8c3f547bf5c02fcfb658c26d982d6176de7f3642cb50ba1dd879fe921.
def localCycle00098 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 25 2, .triangle 16 0, .triangle 0 0, .triangle 1 0, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint fc1151bcd2949019397b88757cb44ef7f00933ca75a9301a2a6fd7566bc57311.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 23 0, .triangle 34 1, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint fe1129aec6ff6e424c335258ac1663213f3074a6f47119e9dfd4a65569334f51.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

def library : Library := fun id => if id < 50 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 37 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))) else (if id < 43 then (if id < 40 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)))) else (if id < 46 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))))))) else (if id < 75 then (if id < 62 then (if id < 56 then (if id < 53 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 59 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))))) else (if id < 68 then (if id < 65 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))))) else (if id < 88 then (if id < 81 then (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)))) else (if id < 84 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))))) else (if id < 94 then (if id < 91 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))) else (if id < 97 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 6, 1, 0, 5], ![3, 2, 6, 1, 0, 4], ![2, 3, 5, 4, 1, 0]], proof := .tail 91 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9728)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![4, 5, 6, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![3, 2, 1, 0, 4, 5]], proof := .low (![27, 70, 52, 28, 93, 57, 22, 53, 78, 43, 20, 4, 0, 19, 74, 64, 21, 47, 87, 55, 69, 66, 7, 16, 83, 63, 46, 44]) }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9729)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 5, 6, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![3, 2, 1, 0, 5, 4]], proof := .low (![27, 70, 52, 28, 93, 57, 22, 53, 78, 43, 20, 4, 0, 19, 74, 64, 21, 47, 87, 55, 69, 66, 7, 16, 83, 63, 46, 44]) }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9730)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 6, 5, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![3, 2, 1, 5, 0, 4]], proof := .tail 14 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9731)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 6, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 6, 1, 0, 4], ![3, 2, 5, 1, 0, 4]], proof := .tail 97 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9732)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 6, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 6, 2, 1, 0, 4], ![3, 5, 2, 1, 0, 4]], proof := .tail 71 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9733)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 6, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![6, 3, 2, 1, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 86 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9734)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 4], ![3, 2, 1, 5, 4, 0]], proof := .tail 6 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9735)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 6, 0, 5], ![3, 2, 6, 1, 0, 4], ![3, 2, 5, 1, 4, 0]], proof := .tail 97 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9736)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 6, 0, 5], ![3, 6, 2, 1, 0, 4], ![3, 5, 2, 1, 4, 0]], proof := .tail 71 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9737)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 1, 6, 0, 5], ![6, 3, 2, 1, 0, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 6 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9738)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 1, 0, 5], ![3, 2, 6, 1, 0, 4], ![3, 2, 5, 4, 1, 0]], proof := .tail 91 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9739)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 1, 0, 5], ![3, 6, 2, 1, 0, 4], ![3, 5, 2, 4, 1, 0]], proof := .tail 91 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9740)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 6, 1, 0, 5], ![6, 3, 2, 1, 0, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 91 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9741)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 2, 1, 0, 5], ![3, 6, 2, 1, 0, 4], ![3, 5, 4, 2, 1, 0]], proof := .tail 85 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9742)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 2, 1, 0, 5], ![6, 3, 2, 1, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 85 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9743)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 2, 1, 0, 5], ![6, 3, 2, 1, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 90 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9744)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![4, 5, 0, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 80 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9745)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![4, 5, 0, 3, 6, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 41 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9746)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![4, 5, 0, 6, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 68 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9747)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![4, 5, 0, 3, 6, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 62 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9748)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![4, 5, 0, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 68 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9749)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![4, 5, 0, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 68 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9750)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![4, 5, 0, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![3, 2, 0, 1, 4, 5]], proof := .tail 68 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9751)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 77 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9752)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 5, 6, 0], ![3, 2, 1, 4, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 8 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9753)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 5, 6, 0], ![3, 2, 1, 4, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 23 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9754)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 6, 5, 0], ![3, 2, 1, 6, 4, 0], ![2, 3, 1, 5, 4, 0]], proof := .tail 36 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9755)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 6, 5, 0], ![3, 2, 6, 1, 4, 0], ![2, 3, 5, 1, 4, 0]], proof := .tail 30 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9756)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 6, 1, 5, 0], ![3, 2, 6, 1, 4, 0], ![2, 3, 5, 4, 1, 0]], proof := .tail 11 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9757)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![3, 2, 1, 0, 4, 5]], proof := .tail 100 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9758)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 5, 6, 0], ![3, 2, 1, 4, 0, 6], ![3, 2, 1, 4, 0, 5]], proof := .tail 58 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9759)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 5, 6, 0], ![3, 2, 1, 4, 6, 0], ![3, 2, 1, 4, 5, 0]], proof := .tail 23 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9760)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 6, 5, 0], ![3, 2, 1, 6, 4, 0], ![3, 2, 1, 5, 4, 0]], proof := .tail 36 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9761)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 6, 5, 0], ![3, 2, 6, 1, 4, 0], ![3, 2, 5, 1, 4, 0]], proof := .tail 30 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9762)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 6, 5, 0], ![3, 6, 2, 1, 4, 0], ![3, 5, 2, 1, 4, 0]], proof := .tail 65 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9763)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 1, 6, 5, 0], ![6, 3, 2, 1, 4, 0], ![5, 3, 2, 1, 4, 0]], proof := .tail 68 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9764)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 1, 5, 0], ![3, 2, 6, 1, 4, 0], ![3, 2, 5, 4, 1, 0]], proof := .tail 11 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9765)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 1, 5, 0], ![3, 6, 2, 1, 4, 0], ![3, 5, 2, 4, 1, 0]], proof := .tail 50 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9766)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 6, 1, 5, 0], ![6, 3, 2, 1, 4, 0], ![5, 3, 2, 4, 1, 0]], proof := .tail 11 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9767)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 2, 1, 5, 0], ![3, 6, 2, 1, 4, 0], ![3, 5, 4, 2, 1, 0]], proof := .tail 76 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9768)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 2, 1, 5, 0], ![6, 3, 2, 1, 4, 0], ![5, 3, 4, 2, 1, 0]], proof := .tail 76 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9769)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 2, 1, 5, 0], ![6, 3, 2, 1, 4, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 10 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9770)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 75 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9771)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 6, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 2 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9772)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 6, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 2 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9773)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 3, 6, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 2 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9774)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 2 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9775)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![5, 4, 0, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 2 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9776)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![5, 4, 0, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![3, 2, 0, 1, 4, 5]], proof := .tail 2 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9777)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 35 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9778)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 1, 6, 0], ![3, 2, 4, 1, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 13 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9779)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 6, 1, 0], ![3, 2, 4, 1, 0, 6], ![2, 3, 4, 1, 0, 5]], proof := .tail 99 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9780)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 1, 6, 0], ![3, 2, 4, 1, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 54 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9781)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 6, 1, 0], ![3, 2, 4, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 23 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9782)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 6, 1, 0], ![3, 2, 4, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 73 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9783)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 6, 5, 1, 0], ![3, 2, 6, 4, 1, 0], ![2, 3, 5, 4, 1, 0]], proof := .tail 61 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9784)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![3, 2, 1, 0, 4, 5]], proof := .tail 35 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9785)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 1, 6, 0], ![3, 2, 4, 1, 0, 6], ![3, 2, 1, 4, 0, 5]], proof := .tail 13 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9786)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 6, 1, 0], ![3, 2, 4, 1, 0, 6], ![3, 2, 4, 1, 0, 5]], proof := .tail 99 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9787)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 1, 6, 0], ![3, 2, 4, 1, 6, 0], ![3, 2, 1, 4, 5, 0]], proof := .tail 54 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9788)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 6, 1, 0], ![3, 2, 4, 1, 6, 0], ![3, 2, 4, 1, 5, 0]], proof := .tail 23 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9789)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 6, 1, 0], ![3, 2, 4, 6, 1, 0], ![3, 2, 4, 5, 1, 0]], proof := .tail 73 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9790)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 5, 1, 0], ![3, 2, 6, 4, 1, 0], ![3, 2, 5, 4, 1, 0]], proof := .tail 61 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9791)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 5, 1, 0], ![3, 6, 2, 4, 1, 0], ![3, 5, 2, 4, 1, 0]], proof := .tail 72 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9792)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 6, 5, 1, 0], ![6, 3, 2, 4, 1, 0], ![5, 3, 2, 4, 1, 0]], proof := .tail 2 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9793)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 2, 5, 1, 0], ![3, 6, 2, 4, 1, 0], ![3, 5, 4, 2, 1, 0]], proof := .tail 26 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9794)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 2, 5, 1, 0], ![6, 3, 2, 4, 1, 0], ![5, 3, 4, 2, 1, 0]], proof := .tail 26 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9795)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 2, 5, 1, 0], ![6, 3, 2, 4, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 3 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9796)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 2, 6], ![5, 4, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 49 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9797)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 6, 2], ![5, 4, 3, 0, 6, 1], ![4, 5, 2, 0, 1, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 1 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9798)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 6, 3, 2], ![5, 4, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 1 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9799)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 3, 6, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 0, 1, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 1 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9800)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 6, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 1 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9801)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![5, 4, 0, 6, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 9 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9802)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![5, 4, 0, 6, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![3, 2, 0, 1, 4, 5]], proof := .tail 1 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9803)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 42 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9804)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 1, 6, 0], ![3, 4, 2, 1, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 95 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9805)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 6, 1, 0], ![3, 4, 2, 1, 0, 6], ![2, 3, 4, 1, 0, 5]], proof := .tail 25 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9806)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 1, 6, 0], ![3, 4, 2, 1, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 60 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9807)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 6, 1, 0], ![3, 4, 2, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 25 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9808)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 6, 1, 0], ![3, 4, 2, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 51 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9809)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![3, 2, 1, 0, 4, 5]], proof := .tail 96 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9810)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 1, 6, 0], ![3, 4, 2, 1, 0, 6], ![3, 2, 1, 4, 0, 5]], proof := .tail 95 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9811)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 6, 1, 0], ![3, 4, 2, 1, 0, 6], ![3, 2, 4, 1, 0, 5]], proof := .tail 25 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9812)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 6, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 6, 2, 1, 0], ![3, 4, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 5]], proof := .tail 56 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9813)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 1, 6, 0], ![3, 4, 2, 1, 6, 0], ![3, 2, 1, 4, 5, 0]], proof := .tail 60 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9814)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 6, 1, 0], ![3, 4, 2, 1, 6, 0], ![3, 2, 4, 1, 5, 0]], proof := .tail 25 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9815)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 6, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 6, 2, 1, 0], ![3, 4, 2, 1, 6, 0], ![3, 4, 2, 1, 5, 0]], proof := .tail 45 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9816)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 6, 1, 0], ![3, 4, 2, 6, 1, 0], ![3, 2, 4, 5, 1, 0]], proof := .tail 51 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9817)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![5, 6, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 6, 2, 1, 0], ![3, 4, 2, 6, 1, 0], ![3, 4, 2, 5, 1, 0]], proof := .tail 17 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9818)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 5, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 6, 2, 1, 0], ![3, 4, 6, 2, 1, 0], ![3, 4, 5, 2, 1, 0]], proof := .tail 94 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9819)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 5, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 5, 2, 1, 0], ![3, 6, 4, 2, 1, 0], ![3, 5, 4, 2, 1, 0]], proof := .tail 39 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9820)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 5, 4, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 5, 2, 1, 0], ![6, 3, 4, 2, 1, 0], ![5, 3, 4, 2, 1, 0]], proof := .tail 1 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9821)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 5, 4, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 5, 2, 1, 0], ![6, 3, 4, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 31 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9822)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 2, 6], ![5, 4, 3, 0, 1, 6], ![5, 4, 2, 0, 1, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 33 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9823)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 6, 2], ![5, 4, 3, 0, 6, 1], ![5, 4, 2, 0, 1, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 92 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9824)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 6, 3, 2], ![5, 4, 3, 0, 6, 1], ![5, 4, 2, 0, 6, 1], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 59 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9825)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 3, 6, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 0, 1, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 5 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9826)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 6, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 0, 6, 1], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 59 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9827)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![5, 4, 0, 6, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 81 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9828)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![5, 4, 0, 6, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![3, 2, 0, 1, 4, 5]], proof := .tail 15 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9829)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 38 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9830)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 29 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9831)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 6, 1, 0], ![4, 3, 2, 1, 0, 6], ![2, 3, 4, 1, 0, 5]], proof := .tail 24 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9832)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 40 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9833)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 6, 1, 0], ![4, 3, 2, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 24 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9834)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 6, 1, 0], ![4, 3, 2, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 82 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9835)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![3, 2, 1, 0, 4, 5]], proof := .tail 88 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9836)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 0, 6], ![3, 2, 1, 4, 0, 5]], proof := .tail 12 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9837)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 6, 1, 0], ![4, 3, 2, 1, 0, 6], ![3, 2, 4, 1, 0, 5]], proof := .tail 24 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9838)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 6, 2, 1, 0], ![4, 3, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 5]], proof := .tail 34 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9839)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 6, 4, 2, 0, 1], ![5, 6, 3, 2, 1, 0], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 84 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9840)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 6, 0], ![3, 2, 1, 4, 5, 0]], proof := .tail 32 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9841)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 6, 1, 0], ![4, 3, 2, 1, 6, 0], ![3, 2, 4, 1, 5, 0]], proof := .tail 24 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9842)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 6, 2, 1, 0], ![4, 3, 2, 1, 6, 0], ![3, 4, 2, 1, 5, 0]], proof := .tail 34 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9843)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 6, 4, 2, 0, 1], ![5, 6, 3, 2, 1, 0], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 32 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9844)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 6, 1, 0], ![4, 3, 2, 6, 1, 0], ![3, 2, 4, 5, 1, 0]], proof := .tail 17 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9845)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 6, 2, 1, 0], ![4, 3, 2, 6, 1, 0], ![3, 4, 2, 5, 1, 0]], proof := .tail 17 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9846)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 6, 4, 2, 0, 1], ![5, 6, 3, 2, 1, 0], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 17 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9847)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 5, 4, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 6, 2, 1, 0], ![4, 3, 6, 2, 1, 0], ![3, 4, 5, 2, 1, 0]], proof := .tail 48 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9848)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 5, 4, 3, 0, 1], ![5, 6, 4, 2, 0, 1], ![5, 6, 3, 2, 1, 0], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 48 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9849)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 5, 4, 3, 0, 1], ![6, 5, 4, 2, 0, 1], ![5, 6, 3, 2, 1, 0], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 37 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9850)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 5, 4, 3, 0, 1], ![6, 5, 4, 2, 0, 1], ![6, 5, 3, 2, 1, 0], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 89 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9851)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![3, 1, 2, 4, 5, 6], ![3, 0, 2, 4, 5, 6], ![3, 0, 1, 4, 5, 6], ![2, 1, 0, 4, 5, 6], ![0, 1, 2, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 98 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9852)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![3, 1, 2, 4, 5, 6], ![3, 0, 2, 4, 5, 6], ![3, 0, 1, 4, 5, 6], ![2, 1, 0, 4, 5, 6], ![0, 1, 2, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 18 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9853)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![3, 1, 2, 4, 5, 6], ![3, 0, 2, 4, 5, 6], ![3, 0, 1, 4, 5, 6], ![2, 1, 0, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 67 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9854)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![3, 1, 2, 4, 5, 6], ![3, 0, 2, 4, 5, 6], ![3, 0, 1, 4, 5, 6], ![2, 1, 0, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 79 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9855)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (9728 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 9728 ≤ id.val) (hhigh : id.val < 9856) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 9728)) = true := by
  let j : Fin 128 := ⟨id.val - 9728, by omega⟩
  have hsum : 9728 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (9728 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard076
