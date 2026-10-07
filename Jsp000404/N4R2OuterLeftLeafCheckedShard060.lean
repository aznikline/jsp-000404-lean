import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard060
open N4R2OuterLeftReplay

-- Cycle fingerprint 006c1a086670eb0adb4816ab3141daddd1cb092fb772ae2740d3149e42bd8754.
def localCycle00000 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 22 1, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0433d5bda752ddf3d187d6c6475a89987a50874b1376c23374808ae8f2c895ad.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 2 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 09968ec055105195a5810b9bfccd60dbd2f6c253d1c11d3d437b3b54510ee340.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 33 2, .corridorLower 3 6]

-- Cycle fingerprint 0a5356e1e572cf5ef7b932698acda976f06d96bada331b389e44f0ffa8cfd1e6.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 0aa225412dcc440902cd650c12713055b13b59e234af9d92f2379a5890c2275d.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 0ad19470ecc086d1f07df4c418ab98ad91ee59178a11a94da91138aff2dc69a1.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint 0cff6ed2e57abedf5c5cee6222a236d8b2cb7fceabe72d59fd0207b3e8a6a5d0.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 0ddbeb6499c5818892c00d9586d30c84b80faf5ae620a0b81b56a4e583aa5a1f.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 2, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 142f6625b360c29a6b0a0479afa7ab31d849a38c288722bd63ad847f4e8e8d21.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 15d0a957a75030efb2cc861e955ccfc32da736704158f85b1a785812f48cf3fb.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 18825fe1c4e18cfe5a8007cd2253a26b04506ed510f84ec9bbf169ce2e8ba9aa.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 1c4c7c46a888e2edc5a8868f26d63bea88ff68217b0f693df1abaf25243180de.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .gapLower 2 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 1ff01974c4f031e6a8dbf8a883a8c983a67c1c851630e4f42acbb17957111887.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint 26e41729c90e2e928a22d487c5543d92086088a0669902f6fed2e788eb8277e7.
def localCycle00013 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 2a2aae511fef7288f857cad7c3f251983d30b4e312587b104c603538096f1906.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 2a871fe4d2c410859559f660896303f255a1ccd34c66ab613dc8526e667ef78d.
def localCycle00015 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 2f44d16be0722942992111c5d8bc198d70004c99d62c1bdf3d2bbf4823cb1182.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 314d335f91cf606b28803fbb47b9f0be5694d7a0bd67a6ea134d4d4fd267f55d.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 33bdddc0e266bbcdf3e9faaaa7bdc135ac49096e2d7112cb11e383918db741cd.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 376a0b0495e32a2aaeb1a0ad74a4669427a4b23d67dfe47799ec1779089d6fd8.
def localCycle00019 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 3ebe9aa80561377cce30251a0952286f9cbd6dba885d128e2ab412162223543a.
def localCycle00020 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 403b91baa420e6df6a56a81b3fc05a90458a4ec560de0fef844af0626efd9900.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 40559f5285a6818f61864abb59d8a2779be696a2fefa7bfe45f48c8e9db413f2.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 40f4bc8b3aa5b09f0fcb787c886ed1313dd51095b65a1c4aa0db6078a6b40c69.
def localCycle00023 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 41a718033d48fd72cf0f2a79e344169e0c76a673341f26a411f1601187469bc4.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 43dd7fa929f42705d280f147b1b9a56373d4a4278bd5fb81fadfe3ccf5c51b54.
def localCycle00025 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![0, 2, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false] }
  origin := ![.triangle 10 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0]

-- Cycle fingerprint 45157a4f1288c9bbb58b27f68986c7710f4e3817b74cf880c107a0d2adc3cfdb.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 2 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 4aeaf14f40de12c99ca4492c5a5d7c141a504c03c63a5b50ca537f9db4a7d28c.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 4b3a91839f14103c2af0d7dc5dceca67a777ed1174ef413984b04fbb525a6348.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .distance 2 4, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, -1, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .triangle 28 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .gapLower 1 3]

-- Cycle fingerprint 4cb35a723ce614f0addbc7ef74608e5af912ad6d5611b0920a4ff7d309197c12.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 4dead85b4a389d8b8770e640b68888fb88d088b82851c52a011ab7e966d4c1f1.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 513eb57b1f5bb53ef34bafd64e7910e9e96dfdda708e7dca429cacc273dbade8.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 0 1, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 5194e5a1c819c71055ac6ebf27d09e77cb0ade5deee65955cdda51e4703700cc.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 51b14c48b48dbb846984c5a31ed77dbad6e80a6fad99d7bc728785777f61b82d.
def localCycle00033 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 58897379b379687d8a0a61c401241ed3277b1fc8d87cfa11ac6d778d73201d54.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 4 0, .triangle 18 1, .triangle 30 1, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 59a0b10ca0a19becf0a7b61f2937e4c2d41559165c4aa5eea62e0d8c6332a6d7.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 5fad12706c4c1de1a4bf135b64db41a2a6ae3bb63a3e1f32053c4dea00ccf224.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .gapLower 3 0]

-- Cycle fingerprint 6127bf8e17c7aff901126dd5f487416b0f8735eb20d782f1584b82709f33347a.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 61f684c3439a4460b6233312ddeb731b96f696e8f1db822237572dda674cc0c9.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 62adccc8300b1959634482ca30bb9abbf9cdd105741569bb44833136e87301e5.
def localCycle00039 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 6b3eadcf563b1f5872e62429536dc7dab8b0f4f75adeee6de15476826b436db7.
def localCycle00040 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 6, .distance 2 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 4 0, .triangle 18 1, .triangle 29 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 6de45e4582c9faa37dc4c7e7381cab853154f42cb3ce757fb664ae33f052bc54.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 6e4ff82922d808740b88ac15fe306a601688bcb1297868b98a4ef8f24c93bcc1.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Cycle fingerprint 738c1475a31f407f36451b984c65f147b5aa4cde34be0de0f699530200e3c7a5.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 6, .distance 2 6, .distance 4 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .triangle 4 0, .triangle 18 1, .triangle 29 1, .triangle 34 1, .triangle 33 0, .gapLower 5 0]

-- Cycle fingerprint 749da69e16b75100e696b68d313d628d1316f966ac86a0678517de32fa0969a5.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 75307921adff37f9c771f41c53f4aa188c55b6a1493dca1fe4aeac6ad732e9e5.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 760d6f74206236b079e443dbe4d3ede6efbe53c0f3c474f17ab87c406a2e595f.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 76de560132522c3835dcc53420feaf609bc7773c347a42870cde82476c6ced05.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 77eb55cc3ac9e603f336be9563063a5b9907de29397bce6549fb5eca0cda7633.
def localCycle00048 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 2, .corridorLower 3 6]

-- Cycle fingerprint 7a5c39c3dd6aef6fe51c65626ee4e4f9f13eb0f1d89dc8c3166e5bc9ef6536d6.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 7dc9f6a86bc4a76823383ed97d353f33eea3ea31f61121399f664af7dd9d796b.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 830cf51919b8422d8a6db568c7e4a2401ab4e9986fffba6435c81fc0b3e86c9d.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 831df0248702e67dfc9d1379b6b2edbed5b89543b2993a6fdf3715ff9574178d.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 2, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 85bdf68d411fbc7523c4c8c92b8337df134025de4b3ad2869074feb0aba4d7b7.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 4, .triangle 2 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 8667d4c9f389fec5bd3f60ce8ea7da291c089b6ec0566b2fc1d8af7e33bf3913.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 3 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 8a12aa9be006de9138e98a93c0d0c7fa7436afc3353ccc69c2f8db1633c4a4ac.
def localCycle00055 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 8a587f70b50aab7a367bdfd1e9f51c2ffcdede6c0a450a5b5508e8cf20fbdcf4.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Cycle fingerprint 8d25f37777f7eebc82af7f47687ce1b076e6b48a128b43ecee31d5bb9fca0885.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 8dc32acbdac1c1410dbf8dd9198733f86a4b16945e73b50daf619dd911dae7fb.
def localCycle00058 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .gapUpper 3 3]

-- Cycle fingerprint 8eb456db86df1e90d35edd49f2462fbc778b768265a64e23223d7c705a161016.
def localCycle00059 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 9261f4635444a370eb8a09c137e910d5e34d349427606ce51443c628123900b6.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 96c98728354897a6a5752df32187d782d7fa26832c1e82e4e04fbe867404e6bc.
def localCycle00061 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 993c9d8548fee0c9da3097e1e6b406b85a0c6a8347593823cd42174608dc84eb.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 99622cdf68afc05e2748b44f724a0f8be25668f4b8bf6bd79ad4b8f6ae8155b1.
def localCycle00063 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 3]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 25 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 26 1]

-- Cycle fingerprint 9a05ec3c9c4b75c5623b2a8fe0b34fc48c934105ff6c50d481e085ca51103f12.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 9a6478bf01e795aa0cdf082723f0ae83d800ecb428f937fca8213deaa433a1a2.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 3 0, .triangle 4 0, .triangle 18 1, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 9b2277e3c72b2f67ffaf20e62419cbb83f3c7ebe5909607c0deeba4b56e12413.
def localCycle00066 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 0 1, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 9b971bb23d70956d0e3106d29d9a4735a61a7d3c6c855ae80e65732d1b576b22.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![0, 2, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false, true, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 2, .triangle 6 0]

-- Cycle fingerprint 9d68f914dcca57797d05c8d2f0bf80153aa4d215b7df03b2a4c99b9edc485153.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 9d83df5e98991fa969d3c5852adb827c8bb30ea8646f523fd12ccd62418b5006.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 9ec1748b08337eab4631f87336110962472349d42889c451576b518c37c436e8.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint a108e128682f304963f69b9321af0f1f76b43213b306cc2986150934e5190ef7.
def localCycle00071 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint a1e0c604c62f4640e649a7ba3ed4722f7b6c9e3565f3834346f80a0c98daa644.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a39d07e4a68fecaec6e1a0de9b3dd006509747042399fd7531b2a2c299873a11.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![0, 2, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, true, false, false, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 6 0]

-- Cycle fingerprint a5fefd5770e0f95137d74db0f9a1d2906a2767eb30143b54009f108a4a587985.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint a9c831301b7763fa37b0e805683f2436fafc5728f085558ed0afaa366a43fb08.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 28 0, .gapLower 2 2, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint b432804b4a29924b13e0498089b58fbd86a84910e76e670c19b32206caefa9b8.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b4f8976f789d2f11b9d65710b09623e834070bef1dacc4e16ba3d6fad9596088.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint bbcc7beb711c92436238ab28c7f32c0ae88b6157929d8735ad2ecedc651db35b.
def localCycle00078 : Cycle where
  length := 16
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 2 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4]
    constant := ![0, -1, -1, 0, -1, -1, 3, -1, 0, -1, -1, 0, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 0, .triangle 29 1, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0]

-- Cycle fingerprint be1f73c526ef8a91f6a7adb9ce9f9845c660c7e4ee28a2972a54a57a8efe8c43.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint be8ac4a57826d013ce514e5363feb9805f6c4427a826baf6e9c76ef3b7b2cb7f.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c55cdfe2403613308600deaf75f6517b3e5e972797fb4f295adc5be4ea85375f.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint c70bb264d0cb21e9a8be3c9dcd2c31c88155a3beeddad631c5177684befa0789.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint c9de61f3135ce791ae047be9c4198f4da2bea3e99eb9c17b8803bde9ba2b1125.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint cce24149288d1815d121a7c5c3ebfed482713bfba44c7c5f790bc09e9d051d7f.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d51ec50daffba6661802137881490e9de00b138b16bb39b6bdc8b6017e26d3a9.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint d9f653c9e2676148f9725936c062aad64247a5e192bae4249028b351744f58ce.
def localCycle00086 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 4, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00087 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint de57e41148d8a4a4fc5a0b693da8fd255450d34c02271fc429f266c261c654a7.
def localCycle00088 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint e20b0d6a11fbd61b25a485c906d5919810e2aa5b8eb3182ea966670ee1649a80.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .distance 2 4, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![-1, -1, 0, 0, -1, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .triangle 28 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 18 0]

-- Cycle fingerprint e27047842767959bdfad06219fc6ffec921e93c2b1ecef9134f455cb5908e9aa.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint e37296b2a682f9f59530ca202e0bd159617c651b075070857bb8aca8e865b3bd.
def localCycle00091 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint e3d3853b62d0c186e216f2129623e66bffc9485170d3e1a8cffaed8f565539d6.
def localCycle00092 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint ee0b7b6bb7037873cbd2f9c8ba0d9a50a17525300931bba0c2cc7a0c00857ea4.
def localCycle00093 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 22 1, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint f12fe4520a400d8d3813ed4e77b986c771d293d85c13b1c98c9b387e64d24bcc.
def localCycle00094 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint f1dba46117372287d9b7fb7560813b4c18108fa71d0c871a8ef2ac4314a908b1.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 2, .triangle 8 0, .triangle 0 1, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint f6a37b91edaea1d3003cb558cad544f2c9d441228593c44b1ba7cf759a35d3f8.
def localCycle00096 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint fb31de0424395eab7b77d05efe74a5a67a29cea23801f00862ee36f9128e593e.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

def library : Library := fun id => if id < 49 then (if id < 24 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))))) else (if id < 36 then (if id < 30 then (if id < 27 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)))) else (if id < 33 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))))) else (if id < 42 then (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)))) else (if id < 45 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))))))) else (if id < 73 then (if id < 61 then (if id < 55 then (if id < 52 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))) else (if id < 58 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))))) else (if id < 67 then (if id < 64 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))) else (if id < 70 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)))))) else (if id < 85 then (if id < 79 then (if id < 76 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none))) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))) else (if id < 82 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none))))) else (if id < 91 then (if id < 88 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)))) else (if id < 94 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![6, 1, 3, 5, 4, 2], ![6, 0, 5, 3, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 0, 5, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 3, 1], ![4, 5, 3, 2, 1, 0]], proof := .tail 64 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7680)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 1, 3, 5, 4, 2], ![6, 0, 5, 3, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 0, 5, 1, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 3, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 44 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7681)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 1, 5, 3, 4, 2], ![6, 0, 5, 3, 4, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 5, 0, 1, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 3, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 33 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7682)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 1, 5, 3, 4, 2], ![6, 0, 5, 3, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 3, 0, 1], ![4, 5, 3, 2, 1, 0]], proof := .tail 81 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7683)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 1, 5, 3, 4, 2], ![6, 0, 5, 3, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 0, 1, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 33 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7684)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 1, 5, 3, 4, 2], ![6, 0, 5, 3, 4, 2], ![6, 5, 3, 4, 0, 1], ![5, 6, 2, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 1, 0]], proof := .tail 65 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7685)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 1, 5, 3, 4, 2], ![6, 0, 5, 3, 4, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 1, 0]], proof := .tail 87 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7686)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 1, 5, 3, 4, 2], ![6, 0, 5, 3, 4, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 0, 1, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 54 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7687)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 1, 3, 4, 5, 2], ![6, 0, 4, 3, 5, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 4, 1, 5], ![6, 2, 0, 3, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 17 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7688)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 1, 3, 4, 5, 2], ![6, 0, 4, 5, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 4, 5, 1], ![6, 2, 0, 3, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 14 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7689)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 1, 3, 4, 5, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 4, 5, 1], ![6, 2, 0, 3, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 19 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7690)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 1, 3, 4, 5, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 5, 4, 1], ![6, 2, 0, 5, 3, 1], ![6, 2, 0, 4, 3, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 75 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7691)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 1, 3, 5, 4, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 5, 4, 1], ![6, 2, 5, 0, 3, 1], ![6, 2, 4, 0, 3, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 75 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7692)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 1, 3, 5, 4, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 0, 5, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 6, 2, 0, 3, 1], ![4, 5, 3, 2, 1, 0]], proof := .tail 8 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7693)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 1, 3, 5, 4, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 0, 5, 4, 1], ![6, 5, 2, 0, 3, 1], ![6, 4, 2, 0, 3, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 4 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7694)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 1, 5, 3, 4, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 5, 0, 4, 1], ![6, 2, 5, 0, 3, 1], ![6, 2, 4, 3, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 91 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7695)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 1, 5, 3, 4, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 6, 2, 3, 0, 1], ![4, 5, 3, 2, 1, 0]], proof := .tail 5 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7696)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 1, 5, 3, 4, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 0, 4, 1], ![6, 5, 2, 0, 3, 1], ![6, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 91 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7697)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 1, 5, 3, 4, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![5, 6, 2, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 1, 0]], proof := .tail 10 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7698)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 1, 5, 3, 4, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 1, 0]], proof := .tail 56 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7699)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 1, 5, 3, 4, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 0, 4, 1], ![6, 5, 2, 0, 3, 1], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 48 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7700)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 1, 4, 3, 5, 2], ![6, 0, 4, 3, 5, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 0, 1, 5], ![6, 2, 3, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 59 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7701)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 1, 4, 3, 5, 2], ![6, 0, 4, 5, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 0, 5, 1], ![6, 2, 3, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 61 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7702)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 1, 4, 3, 5, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 0, 5, 1], ![6, 2, 3, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 92 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7703)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 1, 4, 5, 3, 2], ![6, 0, 4, 5, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 5, 0, 1], ![6, 2, 3, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 35 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7704)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 1, 4, 5, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 5, 0, 1], ![6, 2, 3, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 32 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7705)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 5, 0, 1], ![6, 2, 3, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 53 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7706)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 5, 4, 0, 1], ![6, 2, 5, 3, 0, 1], ![6, 2, 4, 3, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 7 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7707)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 6, 2, 3, 0, 1], ![4, 5, 3, 2, 1, 0]], proof := .tail 84 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7708)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 4, 0, 1], ![6, 5, 2, 3, 0, 1], ![6, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 47 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7709)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![5, 6, 2, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 1, 0]], proof := .tail 38 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7710)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 1, 0]], proof := .tail 42 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7711)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 4, 0, 1], ![6, 5, 2, 3, 0, 1], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 2 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7712)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 1, 4, 3, 5, 2], ![6, 0, 4, 3, 5, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 0, 1, 5], ![3, 6, 2, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 40 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7713)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 1, 4, 3, 5, 2], ![6, 0, 4, 5, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 0, 5, 1], ![3, 6, 2, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 11 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7714)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 1, 4, 3, 5, 2], ![6, 0, 5, 4, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 0, 5, 1], ![3, 6, 2, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 3, 4, 2, 1, 0]], proof := .tail 76 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7715)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 1, 4, 5, 3, 2], ![6, 0, 4, 5, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 6, 2, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 72 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7716)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 1, 4, 5, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 6, 2, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 3, 4, 2, 1, 0]], proof := .tail 76 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7717)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 6, 2, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 3, 4, 2, 1, 0]], proof := .tail 80 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7718)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 1, 4, 5, 3, 2], ![6, 0, 4, 5, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 2, 0, 1, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 4, 2, 1, 0]], proof := .tail 43 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7719)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 1, 4, 5, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 2, 0, 5, 1], ![3, 6, 2, 0, 4, 1], ![3, 5, 4, 2, 1, 0]], proof := .tail 76 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7720)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 2, 5, 0, 1], ![3, 6, 2, 4, 0, 1], ![3, 5, 4, 2, 1, 0]], proof := .tail 80 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7721)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 6, 2, 0, 1], ![3, 4, 6, 2, 0, 1], ![3, 4, 5, 2, 1, 0]], proof := .tail 13 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7722)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 5, 2, 0, 1], ![3, 6, 4, 2, 0, 1], ![3, 5, 4, 2, 1, 0]], proof := .tail 58 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7723)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 6, 2, 0, 1], ![4, 3, 6, 2, 0, 1], ![3, 4, 5, 2, 1, 0]], proof := .tail 34 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7724)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 1, 4, 5, 3, 2], ![6, 0, 4, 5, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 79 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7725)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 1, 4, 5, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 2, 0, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 3, 4, 2, 1, 0]], proof := .tail 76 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7726)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 2, 5, 0, 1], ![6, 3, 2, 4, 0, 1], ![5, 3, 4, 2, 1, 0]], proof := .tail 80 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7727)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 5, 2, 0, 1], ![6, 3, 4, 2, 0, 1], ![5, 3, 4, 2, 1, 0]], proof := .tail 97 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7728)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 1, 4, 3, 5, 2], ![6, 0, 4, 3, 5, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 63 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7729)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 1, 4, 3, 5, 2], ![6, 0, 4, 5, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 0, 5, 1], ![6, 3, 2, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 39 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7730)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 1, 4, 3, 5, 2], ![6, 0, 5, 4, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 0, 5, 1], ![6, 3, 2, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 60 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7731)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 1, 4, 5, 3, 2], ![6, 0, 4, 5, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 5, 0, 1], ![6, 3, 2, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 94 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7732)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 1, 4, 5, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 5, 0, 1], ![6, 3, 2, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 60 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7733)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 5, 0, 1], ![6, 3, 2, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 1 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7734)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![5, 6, 4, 2, 0, 1], ![5, 6, 3, 2, 0, 1], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 1, 0]], proof := .tail 69 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7735)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 1, 4, 5, 3, 2], ![6, 0, 4, 5, 3, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 21 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7736)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 1, 4, 5, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 2, 0, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 49 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7737)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 2, 5, 0, 1], ![6, 3, 2, 4, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 26 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7738)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 5, 2, 0, 1], ![6, 3, 4, 2, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 27 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7739)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![6, 5, 4, 2, 0, 1], ![5, 6, 3, 2, 0, 1], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 1, 0]], proof := .tail 83 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7740)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 1, 5, 4, 3, 2], ![6, 0, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![6, 5, 4, 2, 0, 1], ![6, 5, 3, 2, 0, 1], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 1, 0]], proof := .tail 57 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7741)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 3, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 5, 0, 1, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 23 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7742)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 3, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 5, 0, 1, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 36 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7743)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 3, 2, 4, 6], ![3, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 2, 3, 1, 0, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 86 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7744)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 3, 4, 2, 6], ![3, 5, 0, 4, 1, 6], ![2, 5, 0, 1, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 73 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7745)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 3, 4, 2, 6], ![3, 5, 0, 4, 1, 6], ![2, 5, 0, 1, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 46 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7746)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 4, 3, 2, 6], ![3, 5, 0, 4, 1, 6], ![2, 5, 0, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 67 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7747)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 3, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 5, 0, 1, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 20 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7748)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 3, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 3, 1, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 89 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7749)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 5, 0, 4, 1, 6], ![2, 5, 0, 3, 1, 6], ![2, 4, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 25 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7750)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 5, 0, 1, 6], ![2, 3, 5, 0, 1, 6], ![2, 3, 4, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 0 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7751)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 5, 4, 0, 1, 6], ![2, 5, 3, 0, 1, 6], ![2, 4, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 20 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7752)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 4, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 0, 1, 6], ![3, 2, 5, 0, 1, 6], ![2, 3, 4, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 93 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7753)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 3, 4, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 5, 0, 1, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 20 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7754)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 3, 4, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 5, 0, 1, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 71 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7755)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 4, 3, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 5, 0, 4, 1, 6], ![5, 2, 0, 3, 1, 6], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 25 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7756)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 4, 3, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 5, 4, 0, 1, 6], ![5, 2, 3, 0, 1, 6], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 20 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7757)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 3, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 52 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7758)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![5, 1, 3, 2, 6, 4], ![5, 0, 3, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 52 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7759)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 3, 4, 6, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 1, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 2, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 55 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7760)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 3, 4, 6, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 1, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 2, 3, 1, 0, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 78 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7761)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 4, 3, 6, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 2, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 67 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7762)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 3, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 0, 1, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 55 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7763)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 3, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 3, 1, 0, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 28 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7764)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 4, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 0, 4, 1, 6], ![2, 5, 0, 3, 1, 6], ![2, 4, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 37 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7765)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 4, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 4, 5, 0, 1, 6], ![2, 3, 5, 0, 1, 6], ![2, 3, 4, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 6 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7766)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 4, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 4, 0, 1, 6], ![2, 5, 3, 0, 1, 6], ![2, 4, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 30 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7767)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 4, 3, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 1, 6], ![3, 2, 5, 0, 1, 6], ![2, 3, 4, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 88 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7768)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 3, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 0, 1, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 96 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7769)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 3, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 0, 1, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 3, 1, 0, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 55 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7770)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 4, 3, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 0, 4, 1, 6], ![5, 2, 0, 3, 1, 6], ![4, 2, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 37 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7771)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 4, 3, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 4, 0, 1, 6], ![5, 2, 3, 0, 1, 6], ![4, 2, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 31 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7772)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 3, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 29 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7773)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 3, 6, 4, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 1, 6, 4], ![5, 0, 2, 6, 1, 3], ![4, 2, 3, 1, 0, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 51 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7774)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 3, 6, 4, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 0, 1, 6, 4], ![5, 0, 6, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 77 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7775)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 3, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 0, 1, 6, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 3, 1, 0, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 68 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7776)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 3, 6, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 0, 1, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 3, 1, 0, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 68 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7777)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![5, 1, 3, 2, 6, 4], ![5, 0, 3, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 29 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7778)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![5, 1, 3, 2, 6, 4], ![5, 0, 3, 6, 4, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 0, 1, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 95 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7779)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 4, 6, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 4, 6, 1], ![5, 0, 2, 3, 1, 6], ![4, 2, 3, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 90 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7780)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 4, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 0, 4, 6, 1], ![2, 5, 0, 3, 1, 6], ![2, 4, 3, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 90 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7781)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 4, 6, 3, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 0, 4, 6, 1], ![5, 2, 0, 3, 1, 6], ![4, 2, 3, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 90 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7782)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 4, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 5, 0, 1, 6], ![2, 3, 4, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 16 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7783)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 4, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 4, 0, 6, 1], ![2, 5, 3, 0, 1, 6], ![2, 4, 3, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 3 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7784)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 4, 6, 3, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 4, 0, 6, 1], ![5, 2, 3, 0, 1, 6], ![4, 2, 3, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 9 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7785)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 4, 6, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 5, 0, 1, 6], ![2, 3, 4, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 18 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7786)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 6, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 29 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7787)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 6, 3, 4, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 6, 1, 4], ![5, 0, 2, 6, 1, 3], ![4, 2, 3, 1, 0, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 22 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7788)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 6, 3, 4, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 0, 6, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 77 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7789)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 6, 4, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 2, 3, 1, 0, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 74 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7790)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 6, 4, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 2, 3, 1, 0, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 15 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7791)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![5, 1, 3, 2, 4, 6], ![5, 0, 6, 4, 3, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 0, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 2, 3, 1, 0, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 45 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7792)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 6, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 0, 6, 1, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 3, 1, 0, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 12 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7793)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 0, 4, 6, 1], ![2, 5, 0, 3, 6, 1], ![2, 4, 3, 1, 0, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 74 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7794)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 0, 6, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 3, 1, 0, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 85 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7795)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 5, 0, 6, 1], ![2, 3, 4, 1, 0, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 82 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7796)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 4, 0, 6, 1], ![2, 5, 3, 0, 6, 1], ![2, 4, 3, 1, 0, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 24 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7797)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 6, 4, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 5, 0, 6, 1], ![2, 3, 4, 1, 0, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 50 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7798)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 6, 3, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 0, 6, 1, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 3, 1, 0, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 41 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7799)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 6, 4, 3, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 0, 4, 6, 1], ![5, 2, 0, 3, 6, 1], ![4, 2, 3, 1, 0, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 74 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7800)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![5, 1, 3, 4, 2, 6], ![5, 0, 6, 4, 3, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 0, 6, 4, 1], ![5, 2, 0, 6, 3, 1], ![4, 2, 3, 1, 0, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 85 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7801)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![5, 1, 4, 3, 2, 6], ![5, 0, 6, 4, 3, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 4, 0, 6, 1], ![5, 2, 3, 0, 6, 1], ![4, 2, 3, 1, 0, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 70 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7802)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![5, 1, 3, 2, 6, 4], ![5, 0, 6, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 29 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7803)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![5, 1, 3, 2, 6, 4], ![5, 0, 6, 3, 4, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 0, 6, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 66 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7804)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![5, 1, 3, 2, 6, 4], ![5, 0, 6, 4, 3, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 0, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 3, 1, 0, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 62 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7805)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![5, 1, 3, 4, 6, 2], ![5, 0, 3, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 1, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 3, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 55 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7806)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![5, 1, 3, 4, 6, 2], ![5, 0, 3, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 3, 1, 0, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 28 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7807)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (7680 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 7680 ≤ id.val) (hhigh : id.val < 7808) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 7680)) = true := by
  let j : Fin 128 := ⟨id.val - 7680, by omega⟩
  have hsum : 7680 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (7680 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard060
