import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard081
open N4R2OuterLeftReplay

-- Cycle fingerprint 01d0acc7ca822b340390ab5e795d6a28fd8eabe26815a880827426bf61e9b55c.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 02661c9e5fff843f89cb77ce13310dc2c6cbc9e248741f8d7219caf9f796b572.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 043afe18b0c6d543e435686757d8e013eccd30ca6fe0a9d40d63cb3fdff12f39.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 093ea91870cc0f4d881d1f6f42acd87116b8f01e99569f258103c57e77d6eeaf.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .gapLower 4 5, .triangle 2 0, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 0997d2c22d53de0fea3fab3d1b3a79bfda02464a147d43840805e2e9024456f4.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 1012b91809fec51047a741d186b50ef4e196cb38d1b6e6b4f7c0660bca827518.
def localCycle00005 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 11a567df2682d6d7a490e3a2a396214d453816c1e3b1ebe90c9f3e23583e9753.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 17 1, .triangle 18 2, .triangle 23 1, .triangle 2 0, .triangle 1 0, .corridorLower 1 3]

-- Cycle fingerprint 14d5af635636aab551a545958cfa553e7e8c02bc6632ca462817d9efe8dd4274.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .triangle 26 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 1546a9a38150f9a763cda117ff804c922898917a226ba06532d6037d68eb6bb6.
def localCycle00008 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Cycle fingerprint 154cc6c1d9ee5b3a3ec855178f91ef67e0f4b0abb6d6e73d69d22c736cb25e2b.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint 15f2a6b4c914162526d2ad604df46679a4b816f100bf064bd50e4e21082c7fcb.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 1725be8a7702c4f8f5c1c7f0dbe9d6d8bbc1c4f2086ae5b7b2385fafc4491d64.
def localCycle00011 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, 0, -2, 0, -2, -1, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, false, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 16 2, .gapLower 1 2, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 18b0baeeb6749f12b17ddab2d3dc3c66eeb599aeb2fb815bd8b8b45365b5fff8.
def localCycle00012 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 4 0]

-- Cycle fingerprint 1a01284140047a16ab894672ab90abfb00bfefbb93313cd34d0833490759429f.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 4 0, .triangle 23 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 1aa5bed1b4ce4d995ef6225aeeddc7ff863be231a4238e8e1d7549895955d2f8.
def localCycle00014 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-2, -1, -2, 0, -1, 0, 0, 0, 0, 3, 0, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 4, .triangle 0 0, .gapLower 1 1, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2]

-- Cycle fingerprint 1b0cb4325378509a7d86aff2a3ba559a31c2ce4c9360e1f1e9d6232370a7b4e5.
def localCycle00015 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .corridorLower 4 6]

-- Cycle fingerprint 245a1242b034bffe2146efaee526d844965a512d44017a4b51b348e815e00c92.
def localCycle00016 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, 0, -3, -1, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 246a53e1ce6f084d058ee1efccded2c54da453f42671f3ec4f57b7ae38860b26.
def localCycle00017 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![0, -1, -1, 0, -1, 0, 0, 3, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 4, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0]

-- Cycle fingerprint 2681d063d0880f019411ea5573a94aa59e3cbf288809b1b2a129054a4065ebe6.
def localCycle00018 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 2c641e99e40bff0ce78b46154c7a97c582f79b7832e35f26aced7b661858e6a2.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 2cfe181285471d4731258b0a67983a6f4292b612adf0efac95dbf328aa84e646.
def localCycle00020 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![0, 0, 3, 0, 0, 0, -3, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true, false] }
  origin := ![.thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 2d742eee6e499b71a03c1ebf8094d37bf403476176f8a04888a42ac51ca52a5a.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 2 3, .theta 2, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 3]
    constant := ![0, -1, 4, 0, -2, -2, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 15 1, .corridorLower 2 3, .gapLower 2 6, .gapLower 5 3, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .triangle 1 0]

-- Cycle fingerprint 2fd96c72e73e8d0ef59a56234eb86f685f45346b73eaa8497ff31cfc67467fdf.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 31b1502d7a66f0ed8e930d887d4ab6a14d368b47cda5c1778e4e1e243961e6bb.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 32f0bd8b86142f551689518b318fce8730245e4c67d14f7528ffbb2375ec25f1.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 3364a3004d5b2914286df4cdb174f6a73c77ab1bce6a8a7aca63046f3c79ea04.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 3443c8ab4755bdda257d5ee3b0cc29b0eefd56aa809fc39a04ff1062997f60dd.
def localCycle00026 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -1, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 1 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 363b43382e127b42b5174cf4c7bc3366631c52e0893f243ed12d5f4597998268.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 371bd9c3e2d437ff00a5c7d2a9cfe23e5382a00154896bf8d510b1fe50c255f5.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .gapLower 2 0]

-- Cycle fingerprint 38e9e8fb0f0bdf787a21466f0630f980d9123f063ecb673efaebb4dac49de678.
def localCycle00029 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint 391f2934c136a0135fcc2d46c784293638964f6a2ad68d501e15e0b1124e1876.
def localCycle00030 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 3aba273a64b2028c90b83b55ea389505d313dfb907438d628d48a96df76b6ec8.
def localCycle00031 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -2, 0, -1, 0, 0, 0, 0, 3, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 2 0, .gapLower 1 1, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2]

-- Cycle fingerprint 3bf2ba81dc48f1fdac7d2a750f2bd4416d414d86c8a3aca784be42e3f71cba44.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 0, .gapLower 4 0]

-- Cycle fingerprint 3ea3ea6c2836ee963b393a0d7f1c0b0ce212499aa1f3a8d4feb5fb1954c57920.
def localCycle00033 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 1 0, .corridorLower 1 3, .gapLower 1 6, .triangle 22 1]

-- Cycle fingerprint 4019918e68052cd89b915be81b8a0f298fef1d9eaa9da2deb69231d02d2a1d06.
def localCycle00034 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![0, 0, 3, 0, 0, -1, -3, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, true, false] }
  origin := ![.thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 4 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 41a2df2d5afd24f4d4fa2af402eb8c3a22b088068dfb2c8bd8be88caf9db85f1.
def localCycle00035 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 0 0]

-- Cycle fingerprint 432277761ceb77a4bc8933fd640546aeb25f387dd350e4fce406b5f71319c347.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 43238c2814afdabacf339b8f4efb39a98d86b8f04849bfd72d196035415ce54c.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 2 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 17 1, .triangle 7 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint 46005e162348240d7ebe878281658a026216e929065245b6b0ea819d56216a5b.
def localCycle00038 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 30 1, .triangle 14 0, .triangle 3 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 48641a93e889d2d6997b7425eba8e240f735a80c404da2fde05aa61852c2d3c8.
def localCycle00039 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![2, -1, -1, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 1 0, .gapLower 1 0]

-- Cycle fingerprint 49e1b9ce0b2ffba2b40cb171f003fddb2d5dd933c48450b590d95b1a856d8429.
def localCycle00040 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 0, .corridorLower 2 5]

-- Cycle fingerprint 49e6f658be1500318449714b9de709f7c48510fa1fcb65fe2422797a0fb2e710.
def localCycle00041 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint 4a97bead9eaa845f5a6c82e00a10a4b283ccc058da048a6c13c7740d13a64a7d.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 2 5]
    constant := ![0, -2, 0, -2, -1, -1, 0, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 4df5e838e45ac16a7c1e423709ffd914c45b9c004c172f49e5f9a0e7c685d319.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 500bd699eed5297af4db61bc9da607c949b538ebea09f152b3645506c1ffaace.
def localCycle00044 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, 0, 0, -1, -3, -1, 0, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false, true, true] }
  origin := ![.triangle 17 0, .triangle 18 2, .triangle 23 1, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 5068d8ad4f6a0f26af0fae86066f1ffbc00da79b6de1dc5d477a18eaa3c49a61.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 528c38e6f1e419a4ed10412b712bff207720ca28825e287cbaa23c57db620cc1.
def localCycle00046 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![0, 0, 3, 0, 0, -1, -3, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, true, false] }
  origin := ![.thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 52e95e8ae96b80694ab9e14961faaefa9f49265f2cdb252acb4542fed1a0717f.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 5336a199aec778d4a4a23f18d6e36c62192d417e613cf69569896d0b612d88a1.
def localCycle00048 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, 0, -2, -2, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 53eb732b697aa0cf1889bf9c21a0afb4269715c81a807e1379d7adb756d4527a.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5618a8a664dcf9a7728fe955bdc4f136cfc7c44c4865cdd3e357ad1c5fac3db7.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .gapLower 3 0]

-- Cycle fingerprint 572ccd3f4e756e8609436c6dde686d8f50e9dc45c0f05247511cd067cd320adb.
def localCycle00051 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 5804f84aa5e2c33b16e90e76f620a6825a08986e45a5b85626675e6d10179d6e.
def localCycle00052 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 30 2, .triangle 18 0, .triangle 16 0, .triangle 6 0]

-- Cycle fingerprint 583ad8226a552f83fb0a70d0ce7420e5d2c0853411d080410d5feba8bc54132f.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 2 5]
    constant := ![0, -2, 0, -2, -1, -1, 0, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .triangle 18 1, .gapLower 1 3, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 5c9e0cf2cee2397663c93badbbf0f3244650d1b835604267d5cb7c652e944212.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .gapLower 3 0]

-- Cycle fingerprint 5e9aefc76827e67a07656cd152a6032e6bab9c7884edaf91b21bc8ea0d440f0e.
def localCycle00055 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 5f7af76a216673f45998e01dbbcce5e0a8e7b0bf46d511a989a02af9eb9f5fb6.
def localCycle00056 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 608e5323a6b6cc5a29367aca76ecb932efe3a3382ea5ca04ab9547c3e7201e8c.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 6 0, .triangle 8 0, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 6103b29b302f22305f5910242c5a06f7ffe120eea474edc9c1f3d17781d42919.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 645a53ca3e7464592aec16d25b824c5ce4f1a0ca6db72f4503f35f2433c0b873.
def localCycle00059 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, 0, 0, -1, -2, -2, 0, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false, true, true] }
  origin := ![.triangle 17 0, .triangle 18 2, .triangle 23 1, .triangle 2 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 64825f73b9d41d14940b9a6b9ba3ab5c9983ea9383e4f0431a22f7dadc96932b.
def localCycle00060 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 14 0, .triangle 3 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 658c47b84cf63a171b27ff31c81adafd563bd7a0c2f5b1d8f4c152ceba03bf16.
def localCycle00061 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 6634779f6e89d151d368a9847fe2254e90fe189d36cd7b1e04512d20584c1410.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 682e4352f44b6279a97712d6da7d638db2b65b76ddc4c3dafb60b8a3d7b0439a.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 6a14f77036f2cd9f9d986c5befd8a5904795b7edf1fd889babcd08bcb2d1d4d9.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 6d63a8b98d37d8a13ae19fbf6eb9359f5b39d8b253a2949fd539b09c0df991a1.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 2 1, .triangle 1 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 6e8806e63b83cc063415c54527103e3f0c7c5873917c9dc2fa96e6ee039cc030.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 6eedfc387acc215db88a6ed2ee811299e15fb19401015288acdd8d011ac33b5c.
def localCycle00067 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 3, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 717f01647f103a21f1d3476c703a1a7b16eb28d13fa10c099769ed488ad2828f.
def localCycle00068 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 71e7c8b3ea8096f6843fdb22756fa2a77415f21c73b5db167e1d3dd14da6dc09.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -1, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 1, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 766dc52885521b9765c1f1f6b8f5938036dec94cbd7c9559d4b7877fff73b4f8.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 774c55349f81aec08ea5de3e4defb74a7236b7b253b6616fe412fb6299305c1f.
def localCycle00071 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 7798bc97c00cdae1bc4eb90a9e4bb5d8a61c9b9d758fb0307895f9a4bded4cba.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2]
    constant := ![-1, -3, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0]

-- Cycle fingerprint 795a7905646e7d0eebe61d3318af63e5b936dfb42cf8e274ea2148e19cbc3fd1.
def localCycle00073 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 27 1, .corridorLower 2 3]

-- Cycle fingerprint 79db4109288f7e49a065c295394a5b868799588625bfa133dc05f84e68d86e69.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 7a096c46b956e47f6df5e025ed87b5347172b4f6790fbd14f61b0f3c3a6e8665.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 7a768884402593750c97454535272ed8adeef10489e82fbe12d0f1acacb0a2a5.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 4 6, .gapLower 4 5, .triangle 2 0, .triangle 1 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .gapLower 4 0]

-- Cycle fingerprint 7f71a21734afcf5308d4646abb219f7d5c8e9bc7d3081faac1967eb7563c3cbe.
def localCycle00077 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .gapUpper 2 5]

-- Cycle fingerprint 819a42901b0af107dba48a1c8d03a8f32c91106c68ff77202eda08375b40acb5.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 84bf4307c08fa6d07bc8ac691a09095041f8ad2ad79fb1feb6ff35a17bd57f72.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 85c693370457c7e438ec537f7c30b184eb28910530477e26819961d7915d079c.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 2, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 2, .triangle 8 0, .triangle 6 2, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 8641ba6f8cc8c8b39f8cbc03c1091d0206d7e052790d33206262bf356ff24322.
def localCycle00081 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 894f26d9d851a410e7f19d91b9232a8b59623de9a18a874daea1bea66ec6276f.
def localCycle00082 : Cycle where
  length := 16
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 8b5ad58cec57986e49988b27cd094959d7bb06ee425cbb3ac07ba7e7ca20ee9d.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 6 2, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 8d3eb6efffd999d8c36b3638cc7f3d5815d5098dbab2ae4966b2bc1f92313153.
def localCycle00084 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 8f669d8f2b5d981e47faf703ccde6ef30a5448e5b68a4d7910f6748955c2e97b.
def localCycle00085 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 2, .triangle 30 1, .corridorLower 5 6]

-- Cycle fingerprint 8fd9f745cf96f498bc2ef271a8f7b21ff0f02283cce39d6ef5c8b1979936ce39.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 1 4, .distance 0 1, .distance 0 3, .distance 3 4, .distance 4 6, .distance 3 6, .distance 2 6]
    constant := ![0, -2, -2, -1, 0, 2, 2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true, true, true, true] }
  origin := ![.triangle 18 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 1 2, .gapUpper 3 3, .gapUpper 4 4, .triangle 32 2, .triangle 27 2]

-- Cycle fingerprint 9088b7528948f8b75cbc41e993ce7a86d359bb53d9508f885b0e83c619b8168e.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 90b3e01b63a6d33207564ae1c97a3d962110e21863abfedf6272dafcd5111795.
def localCycle00088 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![0, 0, 3, 0, 0, -1, -2, -2, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, true, false] }
  origin := ![.thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 911ec152470f743fe22485d8e1f15d6f161528f3ca59c4a6a91eddf7eadca2af.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 912420e90eb66b78886163c6c501ee9acf245ad451b47f95d7454a7f4a00cee8.
def localCycle00090 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 3, .theta 1, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 1 0, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 92d80fb9c2dc255a84bd83e168cd951b521583ed2a291047050fdf3f879252e3.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 23 1, .triangle 29 0, .gapLower 4 0]

-- Cycle fingerprint 964310249fb5bbc06a8c44cf531f1eaedadd7db599dd09ac9480e8a999638a76.
def localCycle00092 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 982817356cd44f3c17b3e7d6bc73009e650fdb7edcccc87f41a4127af7176e3e.
def localCycle00093 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 17 1, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 1 3]

-- Cycle fingerprint 982b05b91379c4c0936587eb70c9dbca33fd2e29afe48136993774d9ddf96372.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .triangle 1 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 985cd8c2f2d93e1851058bd5b16ca9e3f9909f1fa5f2b0b0d9c050fd202b0971.
def localCycle00095 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 99a4b437a3a694189e9da2aff5ab30cd04d056271fba69e45ab0f6e3fa7a8937.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 99dc5bc1007ecc2d96eb33f2415d77ecefd66710bb4d654ca17e23b85471d13f.
def localCycle00097 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .triangle 23 1, .triangle 2 0, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 9c787cc7a8a1b2445e1de9b4887a4faf2c5005f0532ba95812a4d446cd8a1ffc.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 2, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint a17ccf9f1b1968eb43782d31f46e447b4300596e301880813e74e823120e7616.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 2, .triangle 24 0, .triangle 30 0, .corridorLower 2 5]

-- Cycle fingerprint a51c5524d7ca31affd759cc3a7880fbe91a8099eda38de6c4a24689959005d63.
def localCycle00100 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3]
    constant := ![-1, 0, 0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 4, .triangle 0 0, .triangle 1 0, .triangle 15 1]

-- Cycle fingerprint a55e6d077f3fe932e39f04bbf1785fd13e1e7ac1f941c6128d9b08ca48587b01.
def localCycle00101 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint a654bc38e4016caf0c0efc5e5a6d1cf60624a94a4ef0f7494c8e883797be7c06.
def localCycle00102 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint a6f05a429d6283426bf253321162f348f06e8d28017e104f9cc0231dea4ed466.
def localCycle00103 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 1 0, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint a7358f2dd86572c358d5ec03007eb1d04d8ec414e4968c8b398ba1e55b6fb268.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint aa8b47c5759b266bb94cd0fc21f2f3bc76eea6456c92fe34b199edf1732c14d5.
def localCycle00105 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 0 1, .distance 1 3, .theta 1, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 0 0, .triangle 1 0, .corridorLower 1 3, .gapLower 1 6, .triangle 24 2]

-- Cycle fingerprint abdb6c127be0d0835f73a9caec7784059a8aa0072551589d0d8b78fd75f37f7a.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint aca866d1f44367f990f00136be989dad60522ea3639b9bff8f5c987e229a58ee.
def localCycle00107 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 2, .triangle 22 1, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b0334f10753ee252b1d050d96770520a92463158767b769c7a59b97b4a976193.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b11747b9c42d03125bca812e424db1edc95c58b75647bd7980465b8e2e7c6279.
def localCycle00109 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 17 1, .triangle 7 0, .triangle 0 1, .triangle 1 0, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint b484a55c37a8dc6d51529324335300ab0b8c2c277659696a7ebe20bf6cfa4103.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![-1, -3, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0]

-- Cycle fingerprint b684dd2939d7496a7e27b71664ae6eba8d7416a7c6f7b6889ebb861b058cf714.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint b93f4005e82b9a5cc298aab52752a08df28ff4d51da776be2074e3379e56c2c3.
def localCycle00112 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .corridorLower 2 3]

-- Cycle fingerprint bb9d01df5a2ddc9305188f5abac18cf1a1c0f6d127632ae97bbc2d57a8bd4cf6.
def localCycle00113 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint bbbaf791f899c881cd8fe583e3e29ae6539d5889465432ab71caaef7aa1c1529.
def localCycle00114 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 2, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 2, .gapUpper 2 3, .triangle 7 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint bcec373ff04500dcfb44250bbcd1121e1d9e6d8c6e9abd18d2fec142b2ed265f.
def localCycle00115 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 0 0, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint bd4f522798825a73b5772221678c23181fa13acaffff0e9c95ad79e0291132e8.
def localCycle00116 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint c11bf8cd396cc82770cf3c9cebb0a60e00f8694018f1c9c11e141d631278a9f9.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint c15596373e38c67a3d2047b720ec1f11a9bccd52172e2d77e2418e865c083178.
def localCycle00118 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .triangle 1 2, .gapUpper 3 3, .gapLower 4 3]

-- Cycle fingerprint c312d1d27e747e982d69279613e54c69f08edccae8a5152936e1db086b3d2a25.
def localCycle00119 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 18 2, .triangle 23 1, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint c7f6451c14b71d4eaa0b6443ee6ed1a38c7ee30a041c0b9aa209ccb7ace0fede.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint c89e5550d91d3f7984f9a8a483b961d73d50a718503d1c44d526b58e081b1384.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2]
    constant := ![-1, -2, -2, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0]

-- Cycle fingerprint c93804c852e23991bdb698f422f5546fc25a74ddaf84f99d9dbd45143f8c804a.
def localCycle00122 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint c97368e73e26d65cfeafe257581a87610abc46099546f76b63cc2d6f59776afe.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint ca4c427f9a834f25188a90d69c40b02da63d7e26ce138c315882f51c8b73055f.
def localCycle00124 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, 0, 0, -2, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, true, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint cf494cf09a3aa3466483ae01565227e7ce47cdd0a76a25f139aabec85b12e36a.
def localCycle00125 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 1, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint cf9d0cd6bda37dde2b4ddcc6472be153188967cd75ca8021ccf898082be9c6ef.
def localCycle00126 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint d0176c55506b7c4de15e8b3fdc9ed9be03ebcb81b9aebc6ccdc0d864153c0ab1.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint d02ecd3177aa34efe9a438b722b2e39c5c88708371188bc4b4ef563a272d1fd4.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint d1b5d1855a334adb9e481720ddbd752e65c0a0fefa04a47562643d0fd1b86403.
def localCycle00129 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, 0, 0, -1, -1, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .triangle 2 0, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint d29df4ad178afc0ef2c66022e3f1e83b9f77a19153724ef9407a7f280b2e67ac.
def localCycle00130 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint d3d7a4ebab533e01d0a75a5f7fbc412e63d97e53f0a445c40de153fe2c1673e3.
def localCycle00131 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint d54bd7cc78c61fdfb0d6387142e166096de01262f98d7fe1d8ac5baca4d67c69.
def localCycle00132 : Cycle where
  length := 15
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint d7cdde6ca0c7b64f17354c7a038db15ec3c96e995b5c12f5bbfc3ffa8b7f33ce.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint d8ee847a341fb69a2bdab32a7d57f1b7635fc368cd075cff3f356b70f343ab27.
def localCycle00134 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .triangle 4 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint d8ff2c789a2531e137817657770c42c33b1ac2beaa9b2738842c1ad98c7923df.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 2 3, .theta 2, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3]
    constant := ![0, -1, 4, -1, -2, -2, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 15 1, .corridorLower 2 3, .gapLower 2 6, .triangle 17 0, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 1 0]

-- Cycle fingerprint d917373b5faba6abc9938871f23f8ffbdb6e3d77522f98cb4875c1187e855527.
def localCycle00136 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 1 0, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00137 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint db91a8ee3a5a810d025af824427d873599fb56bd85752125cba2d24858993a03.
def localCycle00138 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint dbe9579edc561b1b6b7fd65abe23a587cdc4a8cf877cd2d37ed2458ddefbdaae.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 4 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint de45eb866372ce774ee1199f3bfd2b97ac133eb8c0dbd9a68322050a80734b89.
def localCycle00140 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -2, -1, -2, 0, -1, 0, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, true, false, true, true, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 4 0, .gapLower 1 1, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint e1ac13cb6384c46362da24a2aa1332ee54de3548248f13dcce612ffad3af6652.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e6d5c920c2f4109ece066a919eba674becbd3d9ac33c055d8026f11cc8b0d162.
def localCycle00142 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint e770beb1bbb05ba253b5434459921f6012e50477bb61deeb7f4c2f0fa5bfbfb2.
def localCycle00143 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint e9ca0ced7732f2d4dd9cd84bf9b6b70a6c6bad3da16a60d6a28a0a4dddc3ac89.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint f2345b086109c0291a9e1729382a2e3a7aa7834ef6983f92cbcf231d3dbf5643.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 17 1, .corridorLower 2 5]

-- Cycle fingerprint f32adb2da803b9fc42dc63356ba49693198c668c4d7f8f2be72133edb7c52433.
def localCycle00146 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 22 1, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint f3781471defc6647a4131a121ebe38e2efe4e86e45a0e6462d059b2bea10b055.
def localCycle00147 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 23 1, .triangle 29 2, .triangle 30 1, .corridorLower 5 6]

-- Cycle fingerprint f579ee57c0d429d50b78a0b89c5ef1cfdec32cbe32caa6ec762dc8089e1e6f47.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint f5aef9e3ac64ead25c2e4317596f1c643610a6bca2ca426ecd0c0e798c1892a4.
def localCycle00149 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint f5ece3f2ab36612bb6c5b9bf177d9de78aee9e6fba18f1117ae95f8297c52d9c.
def localCycle00150 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint f66783b816dfed319c7a0f242c1f0137b2b00e777a3ba4353011336bbf007da9.
def localCycle00151 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 2, .triangle 17 0, .triangle 0 0, .triangle 1 0, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint f862b1d210faed7f302b620cf09910a7b3bb5ae245c5d01eeb3b200f3fc9280a.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint f9c4f530c8b641e9c7adb327d0b8fce0dc938d40961c93c3149c13a42d6fd14b.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint fa846633d592a37c63bb0a3a322fde9a5e92b4fb9dd6fadf449df418545c143f.
def localCycle00154 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint fb0f5f72e31b7116bf3abbb91685abe11905bb3a346087cbc9a482cbb9f2595c.
def localCycle00155 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint fc809c0aeb3a308f6fdc70622f92af41cf64871aa72c5852c059f7cca0e4317b.
def localCycle00156 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 1 0, .corridorLower 1 3]

-- Cycle fingerprint fc81817b37ab1ff310868912dd1214e511719270222f2c2699624a91409bc3a0.
def localCycle00157 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint fe89f906819b386766991542e06d210443c18b5bb699d74d7986413e58533a5f.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, -1, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 1, .gapLower 1 4, .triangle 4 0]

def library : Library := fun id => if id < 79 then (if id < 39 then (if id < 19 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 14 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)))) else (if id < 16 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))))) else (if id < 29 then (if id < 24 then (if id < 21 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))))) else (if id < 34 then (if id < 31 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))))) else (if id < 59 then (if id < 49 then (if id < 44 then (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)))) else (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))))) else (if id < 54 then (if id < 51 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)))) else (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)))))) else (if id < 69 then (if id < 64 then (if id < 61 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)))) else (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none))))) else (if id < 74 then (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))) else (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))))))) else (if id < 119 then (if id < 99 then (if id < 89 then (if id < 84 then (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))) else (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))))) else (if id < 94 then (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)))))) else (if id < 109 then (if id < 104 then (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)))) else (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none))))) else (if id < 114 then (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)))) else (if id < 116 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))))))) else (if id < 139 then (if id < 129 then (if id < 124 then (if id < 121 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)))) else (if id < 126 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))))) else (if id < 134 then (if id < 131 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)))) else (if id < 136 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)))))) else (if id < 149 then (if id < 144 then (if id < 141 then (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)))) else (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))))) else (if id < 154 then (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)))) else (if id < 156 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![5, 6, 3, 1, 2, 4], ![3, 5, 6, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 1, 5, 6, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 1, 3, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 36 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10368)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![3, 5, 6, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 1, 5, 6, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 1, 3, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 79 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10369)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![3, 5, 6, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 1, 6, 3, 0], ![4, 2, 1, 5, 3, 0]], proof := .tail 137 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10370)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![3, 6, 5, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 6, 1, 3, 0], ![4, 2, 5, 1, 3, 0]], proof := .tail 111 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10371)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![3, 6, 5, 0, 4, 2], ![3, 6, 5, 0, 4, 1], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 2, 1, 3, 0]], proof := .tail 10 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10372)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![3, 6, 5, 0, 4, 2], ![3, 6, 5, 0, 4, 1], ![2, 1, 6, 5, 0, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 2, 1, 3, 0]], proof := .tail 30 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10373)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 3, 5, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 6, 1, 5, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 6, 1, 3, 0], ![4, 2, 5, 3, 1, 0]], proof := .tail 3 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10374)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 3, 5, 0, 4, 2], ![3, 6, 5, 0, 4, 1], ![2, 6, 1, 5, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 123 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10375)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 3, 5, 0, 4, 2], ![3, 6, 5, 0, 4, 1], ![2, 6, 1, 5, 0, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 28 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10376)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 3, 5, 0, 4, 2], ![6, 3, 5, 0, 4, 1], ![6, 2, 1, 5, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 152 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10377)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 3, 5, 0, 4, 2], ![6, 3, 5, 0, 4, 1], ![6, 2, 1, 5, 0, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 157 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10378)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 2, 6], ![3, 5, 0, 4, 1, 6], ![2, 5, 1, 0, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 142 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10379)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 2, 6], ![3, 5, 0, 4, 1, 6], ![2, 5, 1, 0, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 66 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10380)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 6, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 1, 0, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 2, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 116 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10381)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 6, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 1, 0, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 2, 3, 1, 0, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 116 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10382)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 6, 4, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 1, 0, 6, 4], ![5, 0, 2, 6, 1, 3], ![4, 2, 3, 1, 0, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 94 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10383)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 6, 4, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 1, 0, 6, 4], ![5, 0, 6, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 65 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10384)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 3, 1, 2, 6, 4], ![5, 3, 0, 6, 4, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 1, 0, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 116 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10385)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![5, 3, 1, 6, 2, 4], ![5, 3, 0, 6, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 1, 0, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 0, 1, 3, 5]], proof := .tail 116 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10386)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![5, 3, 6, 1, 2, 4], ![5, 3, 6, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 1, 0, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 104 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10387)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![5, 6, 3, 1, 2, 4], ![5, 3, 6, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 1, 6, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 45 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10388)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![5, 3, 6, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 1, 6, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 58 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10389)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![5, 6, 3, 1, 2, 4], ![5, 6, 3, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 6, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 74 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10390)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![5, 6, 3, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 6, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 114 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10391)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 6, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 1 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10392)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 6, 5, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 6, 3, 1, 0], ![4, 2, 5, 3, 1, 0]], proof := .tail 96 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10393)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![3, 6, 5, 0, 4, 1], ![2, 6, 5, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 2, 3, 1, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 144 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10394)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![3, 6, 5, 0, 4, 1], ![2, 6, 5, 1, 0, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 2, 3, 1, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 78 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10395)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![6, 3, 5, 0, 4, 1], ![6, 2, 5, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 2, 3, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 98 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10396)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![6, 3, 5, 0, 4, 1], ![6, 2, 5, 1, 0, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 2, 3, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 76 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10397)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 2, 6], ![5, 3, 0, 4, 1, 6], ![5, 2, 1, 0, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 52 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10398)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 2, 6], ![5, 3, 0, 4, 1, 6], ![5, 2, 1, 0, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 25 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10399)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 6, 2], ![5, 3, 0, 4, 6, 1], ![5, 2, 1, 0, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 3, 2, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 4 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10400)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 6, 2], ![5, 3, 0, 4, 6, 1], ![5, 2, 1, 0, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 3, 2, 1, 0, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 63 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10401)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 6, 4, 2], ![5, 3, 0, 4, 6, 1], ![5, 2, 1, 0, 6, 4], ![5, 0, 2, 6, 1, 3], ![4, 3, 2, 1, 0, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 92 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10402)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 6, 4, 2], ![5, 3, 0, 6, 4, 1], ![5, 2, 1, 0, 6, 4], ![5, 0, 6, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 145 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10403)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![5, 3, 1, 2, 6, 4], ![5, 3, 0, 6, 4, 2], ![5, 3, 0, 6, 4, 1], ![5, 2, 1, 0, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 4 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10404)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![5, 3, 1, 6, 2, 4], ![5, 3, 0, 6, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 1, 0, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 0, 1, 3, 5]], proof := .tail 57 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10405)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![5, 3, 6, 1, 2, 4], ![5, 3, 6, 0, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 1, 0, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 57 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10406)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![5, 6, 3, 1, 2, 4], ![5, 3, 6, 0, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 1, 6, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 7 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10407)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![5, 3, 6, 0, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 1, 6, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 40 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10408)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![5, 6, 3, 1, 2, 4], ![5, 6, 3, 0, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 6, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 0 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10409)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![5, 6, 3, 0, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 6, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 0 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10410)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 6, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 99 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10411)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![5, 6, 3, 1, 2, 4], ![5, 6, 3, 0, 4, 2], ![5, 6, 3, 0, 4, 1], ![5, 6, 2, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 101 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10412)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![5, 6, 3, 0, 4, 2], ![5, 6, 3, 0, 4, 1], ![5, 6, 2, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 40 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10413)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![5, 6, 3, 0, 4, 1], ![5, 6, 2, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 99 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10414)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![6, 5, 3, 0, 4, 1], ![5, 6, 2, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 128 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10415)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![6, 5, 3, 0, 4, 1], ![6, 5, 2, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 87 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10416)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![6, 5, 3, 0, 4, 1], ![6, 5, 2, 1, 0, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 64 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10417)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 27 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10418)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 136 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10419)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 54 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10420)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 143 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10421)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .low (![110, 72, 118, 46, 95, 71, 156, 121, 148, 62, 115, 19, 39, 120, 22, 14, 130, 154, 88, 11, 126, 33, 86, 53, 69, 149, 105, 139]) }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10422)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![110, 72, 118, 46, 95, 20, 156, 121, 148, 62, 115, 26, 39, 120, 22, 14, 130, 154, 88, 11, 126, 33, 86, 53, 69, 149, 105, 139]) }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10423)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 138 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10424)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 17 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10425)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 4, 3]], proof := .tail 141 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10426)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 141 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10427)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 60 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10428)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 4, 3]], proof := .tail 49 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10429)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 6, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 4, 1, 3]], proof := .tail 38 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10430)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 61 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10431)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 4, 3]], proof := .tail 49 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10432)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 6, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 4, 1, 3]], proof := .tail 122 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10433)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 4, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low (![129, 44, 118, 16, 34, 77, 6, 59, 102, 75, 113, 97, 39, 2, 31, 140, 35, 154, 48, 41, 124, 93, 135, 42, 125, 21, 158, 90]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10434)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 4, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 1, 4, 3]], proof := .tail 49 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10435)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 6, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 4, 1, 3]], proof := .tail 131 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10436)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![3, 1, 6, 4, 2, 5], ![3, 0, 6, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 0, 1, 3]], proof := .tail 81 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10437)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![3, 1, 6, 4, 2, 5], ![3, 0, 6, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 0, 1, 3]], proof := .tail 23 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10438)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![3, 6, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 1, 0, 3]], proof := .tail 147 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10439)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 6, 0, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 85 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10440)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 6, 1, 0, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 153 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10441)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![3, 6, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 47 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10442)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 6, 0, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 18 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10443)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 6, 1, 0, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 153 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10444)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 2, 5], ![6, 3, 4, 0, 1, 5], ![6, 2, 1, 0, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 24 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10445)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 5, 4, 6], ![2, 0, 1, 5, 3, 6], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 151 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10446)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 5, 6, 4], ![2, 0, 1, 5, 6, 3], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 150 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10447)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 5, 6, 3], ![0, 1, 2, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 67 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10448)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 1, 2, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 50 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10449)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 2, 4, 3]], proof := .tail 100 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10450)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 2, 4, 3]], proof := .tail 89 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10451)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 89 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10452)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 2, 1, 4, 3]], proof := .tail 117 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10453)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 6, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 2, 4, 1, 3]], proof := .tail 9 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10454)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 2, 1, 4, 3]], proof := .tail 117 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10455)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 6, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 2, 4, 1, 3]], proof := .tail 9 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10456)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 4, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 0, 1, 4, 3]], proof := .tail 119 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10457)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 6, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 0, 4, 1, 3]], proof := .tail 12 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10458)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![3, 1, 6, 4, 2, 5], ![3, 0, 6, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 0, 1, 3]], proof := .tail 8 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10459)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![3, 1, 6, 4, 2, 5], ![3, 0, 6, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 43 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10460)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![3, 6, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 91 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10461)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 6, 0, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 32 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10462)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 6, 1, 0, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 3, 1, 0]], proof := .tail 127 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10463)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![3, 6, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 43 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10464)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 6, 0, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 29 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10465)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 6, 1, 0, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 15 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10466)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 2, 5], ![6, 3, 4, 0, 1, 5], ![6, 2, 1, 0, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 84 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10467)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 103 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10468)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 55 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10469)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 68 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10470)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 146 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10471)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 106 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10472)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 107 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10473)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 109 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10474)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 83 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10475)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 133 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10476)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 80 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10477)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 4, 3]], proof := .tail 37 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10478)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 4, 3]], proof := .tail 108 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10479)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 4, 3]], proof := .tail 49 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10480)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 4, 3]], proof := .tail 49 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10481)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 6, 4, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 4, 1, 3]], proof := .tail 5 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10482)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 6, 4, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 4, 1, 3]], proof := .tail 133 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10483)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 6, 4, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 4, 1, 3]], proof := .tail 122 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10484)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 4, 6, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .tail 73 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10485)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 4, 6, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 1, 4, 3]], proof := .tail 51 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10486)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 6, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 4, 1, 3]], proof := .tail 132 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10487)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![3, 1, 6, 4, 2, 5], ![3, 0, 6, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 0, 1, 3]], proof := .tail 70 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10488)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![3, 1, 6, 4, 2, 5], ![3, 0, 6, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 0, 1, 3]], proof := .tail 134 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10489)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![3, 6, 1, 4, 2, 5], ![3, 6, 0, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 1, 0, 3]], proof := .tail 13 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10490)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![3, 6, 0, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 6, 0, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 82 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10491)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 1, 0, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 56 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10492)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![3, 6, 1, 4, 2, 5], ![3, 6, 0, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 112 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10493)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![3, 6, 0, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 1, 6, 0, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 155 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10494)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 1, 0, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 56 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10495)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (10368 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 10368 ≤ id.val) (hhigh : id.val < 10496) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 10368)) = true := by
  let j : Fin 128 := ⟨id.val - 10368, by omega⟩
  have hsum : 10368 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (10368 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard081
