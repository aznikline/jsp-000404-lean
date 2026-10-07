import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard020
open N4R2OuterLeftReplay

-- Cycle fingerprint 04ebbb7df516471a52b9997f2130fd2ed048dbe3871223d24a08446eaa3c6c59.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 06719814c59f8def6ddface8c3afe8cb0d8f6ab4c7a2e2ee78e2acd85bf15535.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .triangle 1 2, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 08d6808039deed4d39df4ca6b1adb9494552aa0a51072e237a8ce6f91985373c.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6]
    constant := ![-1, -1, 3, -1, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .gapLower 0 4, .triangle 13 0]

-- Cycle fingerprint 090ce61bd34cb8c8fcf15a2e89dccb9538862f6a8a65d3dc89104c273ff2617f.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 0b15f3892f351b312e4f1eb281ae339904c0b284c956d0b5aeb3d0034c5b40bc.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 0b41132e20b44dd78ba4220d3d9138d1ebcc935bbd2a4b2e98e907723e88c725.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 0d957309910edd7067568f46469a7c2e042686da506e1ec0d2ddd4ed6d40a79d.
def localCycle00006 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 0eb16211bdcedbf247d6ae7f19fdcde59e9dc9e585a45e2c2aa9e1f0259880dd.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0ef393964cd49a072133accba5e03b4b3a5ab12adb46f20b87cc1c5102feb36d.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 13e7b5ced78fd0e840d20a53a9fe69c9a062d4700c94298d20eeb4046ff7b89d.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 173f38c38c0c2da8bc000c884e8d290812e71342177261809a2027476d9d4c92.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 19ff47e08800bd65e482b224d3c97012f234a0bff1297e90e58b1ca8232b297a.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4]
    constant := ![0, -1, 3, -1, -1, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 22 0, .triangle 12 0]

-- Cycle fingerprint 1ed7ebd3832082c124356498f8ebb0764e98376258b35da09741088b1e775326.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 4, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 1fcb8758a6300ddb6f252b2b6256c3c24b333f7a61d3a9f2482271bd90c93505.
def localCycle00013 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 28db2d48469496830c523a3b9a3a2174dbd009e0dce30c8791bcee645ec4bd70.
def localCycle00014 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 29f9a214c136ce13df8963c6d04dd67bd59e362ced61f7c877401bc83e4e7e75.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![-1, -2, -2, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 15 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0]

-- Cycle fingerprint 2c994e5e73bdcfcc0d66c2ce87f1e6c585a5ffb8ca9a18b0635f37c1dd34dbb7.
def localCycle00016 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .gapUpper 3 5]

-- Cycle fingerprint 2cc63c30bbeb512ac6b6e692697b7c5209b90f8f61acaeebc76fb63d83e31384.
def localCycle00017 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 2, .gapLower 1 3, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2eeb717854d5534f136cafd416abc919a61db05b565fc8290a620ce26497f572.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 329003f79c053100348d69674c1da371af934bfe0fc74ce50fe11a0663591268.
def localCycle00019 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, -1, 0]
    strict := ![false, true, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 3613446bd866db898dfc7deae3261687f6fdba214c47a60745d5465382b6b8e8.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![-1, -3, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 15 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0]

-- Cycle fingerprint 3b397ac5093c3f277f1a31e6d386d3e24baa43162029346a67861de54f213786.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 3bd7d0dee0a8539d03a783921c7bc91fe7e26857d401614835afe19683b4e597.
def localCycle00022 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 18 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 3c94032430d397154934ca8473ce2ed691be502ae29216a6bebc6818598e9cb7.
def localCycle00023 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3e827d831a8f747d4ea0c74496d92d1759630ac17126bc8a3fba40c0f334c315.
def localCycle00024 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, 0, -2, -2, -1, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .gapLower 1 4, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 40247061bdcaafb0653f67d35491fee6d74f2da72f0b3b86163a3484e8ed4ec2.
def localCycle00025 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 3 6, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, -1, 0, 4, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 22 0, .triangle 31 0, .gapLower 3 0, .gapLower 3 6, .triangle 27 0, .triangle 15 2]

-- Cycle fingerprint 404de070340ec40b7a4cd37f78e8f0f1836e33523357d30c8c9ba1606882d740.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 41ab446f7309657ee74d15d92b4cc91295efea5a631e5eb409f5672a9e278ee6.
def localCycle00027 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 438c947cf768270cffec49666877d88ae5142b763a4d28c95fc965daf93b5986.
def localCycle00028 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 468ef8c8bd31c5535802dc119046cde744a8ec9f6151def4d93ec40b64ba642b.
def localCycle00029 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, 0, 0, -2, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 19 2, .triangle 22 2, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 48ddd1dcd3f047557a1f163f7c94008adcb0eb486968cb17a51e6ac7d13c385b.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 499bfaf7c67f3387904df814c0b570c545a710ef251134d5b635ed77b8248897.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4b829822598ea7d6413eb2eee505522387e7571441516d554de07fb8f4b73e31.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .gapLower 3 0]

-- Cycle fingerprint 4b9a3f191ce618cb30a6a7870e3dcb2f9f57576a3c1902a3c0bd43fe919a3cc0.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4f30657e5caf955a2858525d0f95599a0e11f0b10d048a2c5cdb4cf3b5a459f3.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 50868a204e56eb51ce3b0d4f6c92cd2b5f5c49daefe7cf23fbe61293465ec561.
def localCycle00035 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 512d303df0f5469f664dc71a847ddc85ddbeb8d8c2386742bf10e98853809437.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 54dfb730917bf502f663cd13eec79cd9027ba22b1ba6b0a8fbdab2137e987e22.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .gapLower 1 3, .triangle 17 0, .triangle 28 1]

-- Cycle fingerprint 551b12f3b524fab9e72a76cd74cdbe98fa79b1e959ca82bf998b71ad9b65dde7.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 58c2df332ee1d829d09cc426a2d4f0b5dfec88951d345475ad1a78a5f8cee68c.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 26 1, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5ca08b61d4f3677c994735abef5a215f1f1b58891bd0ec147a6f218ecdc63ebb.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .gapLower 4 3, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 5d0dc6aebf7606da9dd9fd7d1b9230625690f7962f2c71839bfa6a8d87506646.
def localCycle00041 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 5ff02fe104436a3d3bf86c372f8c1eb97e73ff28f245e56910bf43602c702801.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![-1, -3, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Cycle fingerprint 6051babad9d38b4b3686ca4d09b4a7b68e6895f016c93f851517e794a85a6d04.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 62adccc8300b1959634482ca30bb9abbf9cdd105741569bb44833136e87301e5.
def localCycle00044 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 643dc50bd320ea94fee513e05471f03215c68c2d3157e7250f335490d8d29e14.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 65184520d63ddeb9851aae732be4ae7a036bf55a94e6fa6b09a004e082a5f388.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 32 1, .gapLower 4 0]

-- Cycle fingerprint 680c2751dd2fe91a73b09949334e398a1671f14aa2fb33d069de1e363d106990.
def localCycle00047 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 6f26f49e27a72b2433217f4e9cc1baf3090c48523fce58c25b0047a982d8caa3.
def localCycle00048 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 71ca95257ea9f7315ce1df11a4695081af65499ffb3f9059932b60820023c984.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5]
    constant := ![0, -1, 0, -1, -1, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 31 2, .triangle 10 0, .gapLower 0 4, .triangle 13 0, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0]

-- Cycle fingerprint 72954f5bb321ff84b621621a7286b6dbc4c0c1114864d6b573820af62ea530c3.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint 73bc42003671aa0d62bb754e765911b34899ee2c8035d4cad1cfb77408148e68.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 786c56090b0f94fe60ab615e72b384e33270d08b16d0e582b752df215ae23c73.
def localCycle00052 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .triangle 32 2, .gapLower 3 0]

-- Cycle fingerprint 7edd9268646e4dd1d4e4026b8ad593804be7b8bca1cedc70051cc7745864f907.
def localCycle00053 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-2, 0, -1, -1, 0, 0, -2, 0, 0, 3, 0, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 5, .triangle 19 2, .triangle 22 0, .triangle 12 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2]

-- Cycle fingerprint 7f43ef3f1fef2424ba7eaa1b70500360a408de4b4c8b1dff869e4b27b02527d6.
def localCycle00054 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 7fdbfb0ae0e2965fbcbf37425e54a0b94ce7e8af5c85807997151d8e2a5906cd.
def localCycle00055 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 4, -1, -3, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .gapLower 3 6, .triangle 21 0, .gapLower 1 4, .triangle 22 0]

-- Cycle fingerprint 8303b7be626040d661285769c795ee31195d725fb7c621d38ac0fc6490786c14.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 6, .distance 1 3, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 19 2, .triangle 22 0]

-- Cycle fingerprint 85e2fede2d4f310a29ac80cbbe1623691bf41df62cad7a0b8e8e67021b5cb630.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 87f4e38c76c54241caa57b54db7e672f1feca9f42d8af3d65a3a61668ceb1ab6.
def localCycle00058 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8897dec2f2c580d36cd2802fe0a4cf446802c101b668022e7ded7f6fc6b4d284.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![0, 0, 3, 0, 0, -1, -2, -2, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaLower 3, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .gapLower 1 3, .triangle 22 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 8b36ed85753eaa26f6c36a1ac10c5109353563c94ad39856cd8d8e1f6b5a0ec6.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 904ce187d19fcb21caa3ef3f03614ea34eb5c3dabb6af7ba839246582b9e815c.
def localCycle00061 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 4, -1, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .gapLower 3 6, .triangle 21 0, .gapLower 1 4, .triangle 22 0]

-- Cycle fingerprint 935a4de0c9403b56f78e905e2b18be9415550046d717c6d0318374af740a9b7f.
def localCycle00062 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 16 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Cycle fingerprint 97a97a494518cf00afc68ab675d0ef61978b7a75bdfea85fbdef98baba6c2f09.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 97f2b5b2a74233a9df39097ec0610d113527a3fd7388bf84ddf918c9684a43b9.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 3, -1, -1, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 16 2, .triangle 22 0]

-- Cycle fingerprint 9815496836b0ea98285d570cf80e412eb620f65ae10dbf777c2d4e703f473f4c.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 98c8dfeceb4bb63e61d7a35048e14aed82f1dc2aa429f4b514b702e3e06f13eb.
def localCycle00066 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, 0, 0, 0, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 19 2, .triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 9a052708b0cfb6a6d8d0153f15d9c27dc5764a57c19a9125347183a56735bb2e.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint 9cea2578e4894b5eb01c454cabf57306893b371ffc99f97567e1e34c7c675b7b.
def localCycle00068 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 9fadaf0a4d7aa9e6f1ee0b5e507d7db758d0889106d95bc6d002d18585cf50d5.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a142b62b2aafc30b58e49431d2918789999826fb4e21e296a1e9d87e3a299ea4.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a1d313d290fa39b0facc65892fb4adc043d7182c5082d811345dd355e4e6e6dd.
def localCycle00071 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![0, 0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false] }
  origin := ![.triangle 17 2, .triangle 22 1, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Cycle fingerprint a20a249ee47e837583c628d09b65d4a629abe41830cdadda379036b1f74228cd.
def localCycle00072 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 22 2, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint a628bc06d64c8f99ce476dc798690b543856d63069015dc89d32466e6e599a59.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a77122489165686c8444a93240c7fa1b855ea8220b08c7f5e0551b25ff1b4762.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint a79a1fa115c1dc917a782376f15956c6907e08032796746678f057814a618acc.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint a9181db7b3c154cfb246cf74f3b0ddc8991c42e11920e155b70b4d1779f27547.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 22 0, .triangle 12 0, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint ab46fd92e138fc307f7ea6f8e14aebd981e3416bef710661204dfb21f0ad32b5.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4]
    constant := ![-1, 4, 0, 0, -3, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorLower 3 4, .gapLower 3 6, .gapLower 6 3, .triangle 18 2, .gapLower 1 5, .triangle 19 2, .triangle 22 0, .triangle 31 0]

-- Cycle fingerprint ad2f76d02617eadb6fc5ae9b1ecc129ecee73c14b94bfa26dd0b50762b098b04.
def localCycle00078 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint ae7a9d2fff67437f865e58c733e9592f1f1f3b8edc77f9d1568f3dccd9562dc4.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint b36bba6060f76060e82b96e30867bf44447c7d3a4d58ee840200aaa1f44b06d0.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint b432804b4a29924b13e0498089b58fbd86a84910e76e670c19b32206caefa9b8.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b464592f2c9f6688abde1e561f15edac777317bcd9f37e3dbcc6f457e615a1a9.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 2, .gapLower 1 2]

-- Cycle fingerprint b79991a0f6ecd08c1c9b7a42b43dedafe72ba4b2d467d327de713354468889bb.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 22 1, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint bc4ce61628607b953dc3fc7671d80050093d89607d0809d6d4121c37a7d1a8af.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint bc8f33d5985e5756194d6e83afa9d8d0da8ad2df48cd9a5acdc33ea9eb01b390.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3]
    constant := ![-1, 0, -1, 0, 0, 3, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 11 0]

-- Cycle fingerprint bcbe2f3cbff41f09569c2bc09e02c8b4132c0f9130db5e22916366f5e8c7eb48.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 16 1]

-- Cycle fingerprint bd16d12ea9596bdc9c258bf0b7e0b04ca9a942f6a23376a05ad1385ce10122ab.
def localCycle00087 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint bf144a1195d28207667e2d14f12fe281575d109316206e27f7aa3ba80b90f47d.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint c01afb07aa35b287026f5a3945cf6a1f785165c4886127aff655c2900dc5efdb.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint c26f6c23af69fb44bd3609aa2aa6100ebdb880861bd9732176c286a2f969926e.
def localCycle00090 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, 0, -2, 0, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, false, true, false, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 19 2, .gapLower 1 3, .triangle 22 1, .triangle 31 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint c3da40331bee52a627922370eb126630b55b837944ff5c96875758dc71822ee7.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint c4faa0dd71d91dca45ca9e43747caf186c2c377cd4cad820ba41237a62fd7178.
def localCycle00092 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c75e2a7321dbe260b751f6d6bd34b8263ef51ebbe0ac905a6d1aa665eb8f5dd8.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 4 5]
    constant := ![-1, -1, 3, -1, -1, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 16 0, .triangle 28 0]

-- Cycle fingerprint c8d7e11f35c7eefcfb490757b17d6bdcb35ef07541233094915ad9f7b1d6a10e.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint c97d421e6c87b89dc0b81512cff9338f83b4e1f0d5077ab174cb5ec6aca1e013.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint ca6364a95dc1d26ccc2928022cffcc1272c363696e123e3d831a1950ceb5d826.
def localCycle00096 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 2, .triangle 21 1, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint ca97d6bda0e0fb3aba2b7702b3cfe15aca33a5800048e89fb245bdb7cbd4af91.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 1 2, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint caeb3c9b18c2b59577770e13938edb5ede432a5802d8edd6b63fd34587ab1b46.
def localCycle00098 : Cycle where
  length := 14
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint d5351b026d7d12b6a3d41f3a0b649117da9c27dd0444c5da12a983343cbd5ee1.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 2, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint d5a9ed10343d38e1f279c9d0f6c990d1bc8704b699f41789fd5a599420c2d2f9.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint d9021a8d976d0d5a8e74cd28f31eb41e74c41a836aa82555403e8d8a98bf815b.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint db128e1b29ae93b53106f217d49392e31f79dec37d2a1a6718aed19df6da7e05.
def localCycle00102 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Cycle fingerprint dcd5d3cff131c5d67c3617dd31a524e6677e17a2334220a371d48b52230bc4f2.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 6, .triangle 23 1, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint dce26f9a47490dd71b0b7d5fe8f06546009c26be8b9e0b6cd478d3b41286a08a.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint dd3a48891470d53c17fb2b1479789c7ac95957ecf32c596132b136f569dc6f2f.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint de01afb331964e731868dec045e6630dc06ecc79df12c672071b89f66daa9d6b.
def localCycle00106 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 16 2, .gapUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0]

-- Cycle fingerprint e455ef829d2559522643720007fde1ccc5fdadae82422bf88b764bd1c445a063.
def localCycle00107 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint e5f049d2c246f247954b6491b297aa71e43e265e55b044b96175fbac125fb7c7.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 2, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint e67ff67737e6a6b090d0220f4e257373557da3a167542551597cd59a5c9f23bc.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint e83cfddab0ec1be74cf75d48fefdde28a20889286c9ec3d23eb56d9ac7083529.
def localCycle00110 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint ed59a0b5b84f0a1b9bcba3cd2b24759e13f3e0d8e676792bbcc0a2373fe82fd2.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 17 0, .triangle 28 1, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint ed8dfe3a54241ef74b6c99be5cbaae8d26e8c748e2243553aa37d23d6ce1648c.
def localCycle00112 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 0 4, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4]
    constant := ![-1, -1, 0, -1, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.triangle 22 0, .triangle 12 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .gapLower 1 4]

-- Cycle fingerprint f05fcc3405ae6ccde09da54a6b8f5205fdbc34a5e8b2739869f37caac016c829.
def localCycle00113 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f150b1fc1433ae759aae0332701eabecfcbc83a841a621cd4b309559c2429bd6.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f18917f4fae1e2e9028f3886260be07e19dd36793ab9ea079696b6a4528ad85c.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint f2761e356f42e52237c9b9141dc4ccdf04a25ce2cd5f70cc9d8784702b30efda.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint f4a5d2270ffeb17c15275bef0f148d71c4aa3bfb1ab0448cdf6fc72de311dbc8.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint f4ce2b74d44805c60f2bd063a4f22bf121796ccbc3105d7bbfc2a9f7ee9b4a9e.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint f688318c554d03945d75815ae3886b40d74cc74c6eafec419ca82025e7b570f8.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 28 1, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f6da4664ee310d76b245729828857409e8103026ecfac1b219e002e0b6c20e64.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint f87f79d2d85404133ad8a3312c71edefa93df520e4e017889efc7a7a208a0615.
def localCycle00121 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 8 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fac7eb8c9a134418bc3827766de9f2dc3d79a90ec1126a20f1f8701245b9a3f4.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![2, 0, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 23 1, .triangle 22 0, .triangle 12 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint ff14c7fac7b277907bac8470a5f5c512df28068808ef056ce00797fcda79dcf9.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

def library : Library := fun id => if id < 62 then (if id < 31 then (if id < 15 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 11 then (if id < 9 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none)) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))) else (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))))) else (if id < 23 then (if id < 19 then (if id < 17 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none))) else (if id < 21 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)))) else (if id < 27 then (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))) else (if id < 29 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))))) else (if id < 46 then (if id < 38 then (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)))) else (if id < 42 then (if id < 40 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))))) else (if id < 54 then (if id < 50 then (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))) else (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)))) else (if id < 58 then (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))) else (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))))))) else (if id < 93 then (if id < 77 then (if id < 69 then (if id < 65 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 67 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))) else (if id < 73 then (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))))) else (if id < 85 then (if id < 81 then (if id < 79 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 83 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)))) else (if id < 89 then (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))) else (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)))))) else (if id < 108 then (if id < 100 then (if id < 96 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)))) else (if id < 104 then (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))) else (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))))) else (if id < 116 then (if id < 112 then (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))) else (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)))) else (if id < 120 then (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))) else (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 3, 5, 1], ![4, 6, 0, 2, 5, 1], ![3, 0, 2, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 6 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2560)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 3, 5, 1], ![4, 6, 0, 2, 5, 1], ![3, 0, 6, 2, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 65 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2561)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 3, 5, 1], ![4, 6, 0, 2, 5, 1], ![3, 0, 2, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 3, 0, 2, 4, 1]], proof := .tail 70 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2562)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 3, 5, 1], ![4, 6, 0, 2, 5, 1], ![3, 0, 6, 2, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 3, 0, 4, 2, 1]], proof := .tail 81 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2563)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 1, 2, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .tail 117 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2564)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 1, 6, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 0, 1, 4, 2]], proof := .tail 68 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2565)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 1, 6, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 3, 0, 1, 4, 2]], proof := .tail 74 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2566)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 4, 2, 6, 5, 3], ![0, 4, 1, 6, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 2, 1, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .tail 117 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2567)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 6, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 0, 4, 1, 2]], proof := .tail 48 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2568)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 6, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 3, 0, 4, 1, 2]], proof := .tail 114 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2569)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 6, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 3, 0, 4, 1, 2]], proof := .tail 105 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2570)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 4, 6, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 2, 1, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 117 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2571)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 6, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 98 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2572)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 6, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 3, 0, 4, 2, 1]], proof := .tail 114 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2573)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 2, 6, 1, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 109 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2574)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 6, 2, 1, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 78 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2575)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 6, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 3, 0, 4, 2, 1]], proof := .tail 14 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2576)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 2, 1, 6, 5], ![6, 0, 3, 2, 1, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 50 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2577)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 2, 6, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 50 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2578)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 6, 2, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 35 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2579)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 6, 5, 1, 2], ![6, 0, 3, 4, 2, 1], ![5, 3, 0, 4, 2, 1]], proof := .tail 46 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2580)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 5, 4, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 2, 6, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 0, 2, 4, 1]], proof := .tail 67 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2581)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 6, 2, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 0, 4, 2, 1]], proof := .tail 32 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2582)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 0, 6, 5, 2, 1], ![6, 0, 3, 4, 2, 1], ![5, 3, 0, 4, 2, 1]], proof := .tail 118 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2583)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 6, 0, 5, 2, 1], ![3, 0, 2, 1, 6, 5], ![6, 0, 3, 2, 1, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 69 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2584)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 6, 0, 5, 2, 1], ![3, 0, 2, 6, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 41 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2585)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 6, 0, 5, 2, 1], ![3, 0, 6, 2, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 69 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2586)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 6, 0, 5, 2, 1], ![3, 0, 2, 6, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 0, 2, 4, 1]], proof := .tail 69 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2587)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 6, 0, 5, 2, 1], ![3, 0, 6, 2, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 0, 4, 2, 1]], proof := .tail 81 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2588)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 6, 0, 5, 2, 1], ![3, 0, 6, 5, 2, 1], ![6, 0, 3, 4, 2, 1], ![5, 3, 0, 4, 2, 1]], proof := .tail 31 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2589)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 0, 1, 2]], proof := .tail 19 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2590)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 4, 0, 1, 2]], proof := .tail 2 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2591)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 5, 4, 3], ![4, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 3, 4, 0, 1, 2]], proof := .tail 49 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2592)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 0, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 4, 0, 1, 2]], proof := .tail 101 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2593)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 0, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 3, 4, 0, 1, 2]], proof := .tail 110 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2594)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 3, 4, 0, 1, 2]], proof := .tail 95 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2595)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 100 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2596)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 22 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2597)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 5, 4, 3], ![4, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 3, 4, 0, 2, 1]], proof := .tail 49 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2598)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 0, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 101 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2599)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 0, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 3, 4, 0, 2, 1]], proof := .tail 110 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2600)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 3, 4, 0, 2, 1]], proof := .tail 95 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2601)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 0, 3, 4, 2, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 79 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2602)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 0, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 113 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2603)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 6, 0, 2, 1, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 12 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2604)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 0, 2, 1, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 78 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2605)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 0, 2, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 35 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2606)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 0, 2, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 32 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2607)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 0, 5, 2, 1], ![6, 0, 3, 4, 2, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 40 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2608)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 1, 5], ![4, 6, 0, 2, 1, 5], ![3, 6, 0, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 116 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2609)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 1], ![4, 6, 0, 2, 1, 5], ![3, 6, 0, 2, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 39 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2610)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 3, 5, 1], ![4, 6, 0, 2, 5, 1], ![3, 6, 0, 2, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 7 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2611)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 6, 0, 5, 2, 1], ![3, 6, 0, 2, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 73 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2612)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 3, 5, 1], ![4, 6, 0, 2, 5, 1], ![3, 6, 0, 2, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 81 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2613)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 6, 0, 5, 2, 1], ![3, 6, 0, 2, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 81 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2614)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 6, 0, 5, 2, 1], ![3, 6, 0, 5, 2, 1], ![6, 0, 3, 4, 2, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 92 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2615)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 0, 1, 2]], proof := .tail 1 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2616)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 5, 3], ![6, 4, 0, 1, 5, 2], ![6, 3, 0, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 0, 1, 2]], proof := .tail 4 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2617)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 5, 4, 3], ![6, 4, 0, 1, 5, 2], ![6, 3, 0, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 88 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2618)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 0, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 0, 1, 2]], proof := .tail 30 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2619)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 0, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 88 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2620)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 60 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2621)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 121 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2622)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 5, 3], ![6, 4, 0, 1, 5, 2], ![6, 3, 0, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 4 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2623)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 5, 4, 3], ![6, 4, 0, 1, 5, 2], ![6, 3, 0, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 0, 2, 1]], proof := .tail 88 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2624)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 0, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 30 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2625)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 0, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 4, 3, 0, 2, 1]], proof := .tail 88 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2626)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 4, 3, 0, 2, 1]], proof := .tail 60 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2627)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 0, 3, 4, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 8 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2628)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 0, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 106 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2629)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 5, 3], ![6, 4, 0, 1, 5, 2], ![6, 3, 0, 2, 1, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 115 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2630)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 0, 2, 1, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 30 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2631)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 0, 2, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 28 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2632)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 0, 2, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 120 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2633)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 0, 5, 2, 1], ![6, 0, 3, 4, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 52 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2634)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 1, 5], ![6, 4, 0, 2, 1, 5], ![6, 3, 0, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 104 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2635)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 1], ![6, 4, 0, 2, 1, 5], ![6, 3, 0, 2, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 80 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2636)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 3, 5, 1], ![6, 4, 0, 2, 5, 1], ![6, 3, 0, 2, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 44 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2637)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![6, 4, 0, 5, 2, 1], ![6, 3, 0, 2, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 123 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2638)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 3, 5, 1], ![6, 4, 0, 2, 5, 1], ![6, 3, 0, 2, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 36 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2639)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![6, 4, 0, 5, 2, 1], ![6, 3, 0, 2, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 123 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2640)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 6, 4, 3, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![6, 4, 0, 5, 2, 1], ![6, 3, 0, 5, 2, 1], ![6, 0, 3, 4, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 107 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2641)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 5, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 33 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2642)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 5, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 1, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 87 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2643)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .low (![42, 20, 47, 54, 55, 77, 103, 15, 89, 18, 86, 53, 122, 84, 17, 25, 66, 45, 63, 72, 29, 82, 59, 90, 83, 24, 61, 56]) }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2644)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 102 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2645)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 2, 1, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 58 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2646)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 2, 3, 6], ![0, 4, 5, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 27 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2647)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 2, 3, 6], ![0, 4, 5, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 2, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 23 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2648)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 5, 2, 1, 6], ![3, 0, 4, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 43 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2649)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 5, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 3 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2650)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 2, 1, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 62 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2651)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 2, 3, 6], ![0, 4, 5, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 71 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2652)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 99 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2653)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 119 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2654)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 6, 5, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 97 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2655)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 6, 4, 5, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 85 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2656)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 5, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 10 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2657)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 5, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 108 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2658)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 13 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2659)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 16 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2660)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 11 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2661)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 112 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2662)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 57 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2663)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 0 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2664)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 37 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2665)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 2, 1, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 91 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2666)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 5 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2667)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 6, 5, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 94 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2668)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 2, 3, 6], ![0, 4, 5, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 111 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2669)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 2, 3, 6], ![0, 4, 5, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 111 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2670)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 2, 3, 6], ![0, 4, 5, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 2, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 64 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2671)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 5, 2, 1, 6], ![3, 0, 4, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 93 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2672)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 4, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 75 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2673)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 4, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 119 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2674)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 4, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .tail 51 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2675)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 6, 4, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 4], ![0, 3, 1, 5, 4, 2]], proof := .tail 85 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2676)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 5, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 10 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2677)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 38 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2678)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 13 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2679)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 4, 2], ![0, 3, 1, 5, 4, 2]], proof := .tail 96 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2680)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .tail 26 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2681)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 1, 4, 2]], proof := .tail 85 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2682)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 6, 1, 4, 2], ![0, 3, 5, 1, 4, 2]], proof := .tail 21 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2683)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 4, 1, 2]], proof := .tail 34 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2684)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 4, 2], ![0, 3, 5, 4, 1, 2]], proof := .tail 9 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2685)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 75 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2686)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 76 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2687)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (2560 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 2560 ≤ id.val) (hhigh : id.val < 2688) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 2560)) = true := by
  let j : Fin 128 := ⟨id.val - 2560, by omega⟩
  have hsum : 2560 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (2560 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard020
