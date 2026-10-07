import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard094
open N4R2OuterLeftReplay

-- Cycle fingerprint 000f40cf51e2080e523dab2723322d7d0c97aebfd2348c17aac0c689c3069824.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint 02661c9e5fff843f89cb77ce13310dc2c6cbc9e248741f8d7219caf9f796b572.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 0a9674672e7cdfb217e8449fc067e0f98188688b5730922e240e6861d93ba8d7.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 12a0e962b966e3c2c36b51b77065202471f80d3d694539c4af9ebe7603c9ab97.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 4]
    constant := ![-1, -1, -1, 3, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 23 0, .triangle 29 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 20 0, .gapLower 1 2]

-- Cycle fingerprint 170390888142f80ddf98b32c07bc4aabd4bcc1de3623b038d3f38451912c13fd.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .gapLower 5 0]

-- Cycle fingerprint 193fc30f05f2e356f00afe6091d9efb80efaad649908374d927e656c18db72ab.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 1b3cdedd12018915c199c0174bafeef21eeb08cdaabb2e3625f9662f5fe01e38.
def localCycle00006 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 4]
    constant := ![4, 0, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 20 0, .triangle 26 0, .triangle 25 0, .gapLower 4 0]

-- Cycle fingerprint 1d741fc55c8f1fa1dae59fc5d527dc53a0c66dde05a4c93d0063e135eeb0c840.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 0, .triangle 26 0, .triangle 27 2, .triangle 29 1, .gapLower 2 0]

-- Cycle fingerprint 1effbce402d92b63e71ffbba87d35df70711c989b6dcce1f204c1147194ad8aa.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 19 2, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 20cb718eb4cd342e5b73dbbdeb394c6244b9996f1b29d28f41fd3d822ed7e495.
def localCycle00009 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 25d8494c9596865e5a0dcb565f06365b657a8de8e62dd9de2955c63609e5f575.
def localCycle00010 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 2, .triangle 12 1, .triangle 13 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 2c4ffb909e53887330cbe4d9e85fda078dc91f49c42e44a89306144e05fe4495.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 2, .triangle 12 1, .triangle 13 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 2e724dcdcee8aa07df8c971ff6ff87d1d87eb6075c83614da0abb091745f6dce.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 2ef55d037d45144fd8f8f258f8384e884367e556c0bc6b3512dcad78f61f9a55.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 14 0, .triangle 24 0, .triangle 17 1, .triangle 26 1, .corridorLower 2 3]

-- Cycle fingerprint 36ee0530e01cceaf69d100e5ffbb72903d2de864e495623c83259b39622ee880.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 2, .triangle 22 1, .triangle 23 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 3706c36943fd8110178ebd12ddb7bf5f2bcb0ea2ece1045abad3079acf54caf0.
def localCycle00015 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 21 2, .triangle 24 1, .triangle 30 0, .triangle 26 1, .corridorLower 2 3]

-- Cycle fingerprint 39b171f577d7ae42e9d0f85a78b0e87cc349cb793c74e92085116aee9712ca49.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 3e811402cd64650df8f77a3294dd98fb5949a0239c90b7fb0928caeb92340b5d.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 3 0, .triangle 1 2, .triangle 11 0, .triangle 21 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 432277761ceb77a4bc8933fd640546aeb25f387dd350e4fce406b5f71319c347.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 43407a498e3067f4dac77408b433fd32ae17619de6ba531bdc3bd490b6a13eb1.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 465a004c7f309384d0414d27e10ee12ebb55a47d1b01b404c773fcb1176f9252.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 2, .triangle 22 1, .triangle 23 0, .triangle 29 0, .gapLower 2 0]

-- Cycle fingerprint 47cd2eb903715efa239331b32de3a77b70087ac302ee1534d997fb20394ce51d.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .corridorLower 3 6, .thetaNext 2]

-- Cycle fingerprint 4bb461fa22d560ff2a2e5650e6d2470760b00500c5b73343da8916f25397d7c4.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4f803f49cc4c33513781a26c29c4936846f889807af029eb4f1406514928e77c.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -1, 0, 2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true, true, false] }
  origin := ![.triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 2, .gapUpper 2 4, .gapUpper 2 5, .triangle 0 0]

-- Cycle fingerprint 4ff463f28ed79c82aa3c021b5fbf82fbbbf25e20a54fb36a0d8d92dfa2d3af3a.
def localCycle00024 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 5068d8ad4f6a0f26af0fae86066f1ffbc00da79b6de1dc5d477a18eaa3c49a61.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 52de71025268ebf2f6e3cf5a013566dd3d4cda34f20c3365ac4cd507cfdd4170.
def localCycle00026 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 547d05d4894cc38a9d7ff879434c50a1858daab71f50543706f428d6e765cc2c.
def localCycle00027 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 5f7af76a216673f45998e01dbbcce5e0a8e7b0bf46d511a989a02af9eb9f5fb6.
def localCycle00028 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 654080d14678ce61ea1ede2e2039f2096a2db7cdcc8ffb63b6649e09afd7cdf6.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 26 0, .gapLower 2 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 65edfb53be620d6ac83cad8447a49f552163d5e2562273d79bf6d8f7cf2bb38c.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 30 0, .triangle 26 1, .corridorLower 2 3]

-- Cycle fingerprint 6b14ab100411efc772c23dfec3dde76d0095cb1c5399a2e634dc9229f58337a6.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 2, .triangle 22 1, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 704316604dd8de4020255e26ba435aed783196e83697096595e0f0ca32d236f5.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 74d62cbe2411ed006e00d63f018836326a8c62ecc6928146a3899d29e5fabcb9.
def localCycle00033 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 78f6b1352276eb827935fe91744b93ea7262fa27c8dc447fae466256746b809f.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 0, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint 79db4109288f7e49a065c295394a5b868799588625bfa133dc05f84e68d86e69.
def localCycle00035 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 7ef3035bfab67867d9ef18eda2d0506b6447934c3c06ef3feb44ea8194381991.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 80aec984f5fab4c6e95ec46c7add57ae6c88e47713445c14a0b8f60a89cb196a.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 826743fe324aac9f82a52e3dcdf653cb224a54e32bfd479b12f99e80b377d923.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 10 1, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 85d3d09134f6d9be52b1ef1e8ad2e1ee579729da7304e75bcac9b5a722eac100.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint 888b78bd6ed6dec910f1a377eaf3c641d6781294d040f7f9557174573a09e5d3.
def localCycle00040 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint 8ce559f84fcd5d8d620b1b6741107c147f8f3864978d29872010e1e7541bcc31.
def localCycle00041 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 8ec9620e855a0a0c37ac82f80db9adc0f73615fd66bfab079f6f7159720e8171.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8f49e5a5c5deaf3d63cd1871d978528910cba9094df37ea027098faca0b48ec1.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 14 0, .triangle 3 1, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 9231a25a7cdaa003ead65f63abaa99e31881fc20b8b94fd632370eeae1ddcd84.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 92703b9f4575f3c145ad9515697b7d73ef66a1c940bc9c9f95fa01eeb7f047ea.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 96508f815393d2f4921549b46f386251dd5d000703c3666bc8c6d811bbf57ec7.
def localCycle00046 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 99622cdf68afc05e2748b44f724a0f8be25668f4b8bf6bd79ad4b8f6ae8155b1.
def localCycle00047 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 3]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 25 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 26 1]

-- Cycle fingerprint 9e8783bcd52af3f94f3a1d04ffe26f50c5ca2881d92d5ca12b98969045059155.
def localCycle00048 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint a1844c629bb55951e96141bf955f45a883a41e200dbb097d0d7d29f7e2449f6a.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .distance 2 6, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 0, .triangle 26 0, .triangle 27 2, .gapLower 2 0]

-- Cycle fingerprint a19a1c4827c8af7e53feb8c76d1081e299f8ad805b76666255268379d928dc47.
def localCycle00050 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint a7358f2dd86572c358d5ec03007eb1d04d8ec414e4968c8b398ba1e55b6fb268.
def localCycle00051 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint ab6f9b3fa7a715d3d0dc3c1b7423cb6583420e9b9ebaf736b4cd423fead628c1.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 30 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint abc1e3049bf4958eb4a23118aa68d345b3b3485d7777acbdb7c5abf45f017627.
def localCycle00053 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint ad1867f3b6ceae861c4a594672262af2130d80931bb1f610a473c689703d9d1a.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint af3c5ef7ed748763f8f58a2082c2653df2f42a9cb6bf2a70bbdb9312cb88b5ad.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b66023b64177f34dc711e9ec386175286c87b4fe099aec577de82abcae5758a3.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint b70e7bee4f8aa28971ccaabd7a4f387c26ad745dc6104f1331a4d8ea278547c1.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 24 1, .triangle 30 0, .triangle 26 1, .corridorLower 2 3]

-- Cycle fingerprint b7e689b924b87a8688119cd346ab209c8f9bc1b128f2b524e7fa163445556edb.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 2 3, .distance 3 4, .theta 4]
    constant := ![4, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 24 2, .triangle 4 0, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 15 1, .triangle 25 0, .gapLower 4 0]

-- Cycle fingerprint b924396a08f0c31c17d2ea66f2e7718976683a017f50ea18c749bd8f51e316ab.
def localCycle00059 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 10 1, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint bbb053a30d4be082280e91907473fb43ba2648541d92ebe607f63d5ad3b229f8.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint bc6f944ce00188cfe50cc1b49e20d41c0476b8590da2aa7d7da25412b30f7935.
def localCycle00061 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint bd4f522798825a73b5772221678c23181fa13acaffff0e9c95ad79e0291132e8.
def localCycle00062 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint bdeddf96620f2ddc91c3b81d51a6992874497fb5681125ee1b29b8adcc4e0af0.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c1a69647f8a1cde4d8bebb38857d15eefe4c99c34526b1befc883d928dc97682.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint cc359d8e43b5db3619b919664ca7c9ff0eaee3766673799e985f923363f23fcf.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint ce3951f64f56dc03e9031b964ebd383ccd621b33ff1574ad448e57067769ad2c.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 21 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint dafa7ffa188e689c5c9f4937ceeb806acf99db5f45c713e5ab89114e63ca73af.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint e255bb50495f4824c12ba1f6026f27c3cc9d7ec7a744f7f102e7a189a1aae7dc.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .triangle 4 0, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint f0a16a839d7819065afc19c09bdd7adc7f4dc64f3905de36283a07007601b011.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 20 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint f7b50c2945037898ee34e8412c4a2d11d3d11e23db84732ce5a233fba81042d7.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 2, .triangle 12 1, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

def library : Library := fun id => if id < 35 then (if id < 17 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))))) else (if id < 26 then (if id < 21 then (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))))) else (if id < 30 then (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))))))) else (if id < 53 then (if id < 44 then (if id < 39 then (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))))) else (if id < 48 then (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))) else (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))))) else (if id < 62 then (if id < 57 then (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))) else (if id < 59 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))))) else (if id < 66 then (if id < 64 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))) else (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![4, 3, 1, 5, 6, 2], ![4, 3, 0, 5, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![2, 0, 1, 3, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 32 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12032)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![4, 3, 1, 5, 6, 2], ![4, 3, 0, 5, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![2, 0, 1, 3, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 0 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12033)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 3, 1, 5, 6, 2], ![4, 3, 0, 5, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 0, 1, 6, 3, 4], ![2, 0, 1, 5, 3, 4]], proof := .tail 40 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12034)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 3, 1, 5, 6, 2], ![4, 3, 0, 6, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 1, 3, 4]], proof := .tail 43 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12035)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 3, 1, 6, 5, 2], ![4, 3, 0, 6, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 1, 3, 4]], proof := .tail 19 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12036)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 3, 1, 6, 5, 2], ![4, 3, 0, 6, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .tail 32 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12037)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 3, 6, 1, 5, 2], ![4, 3, 6, 0, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 1, 0, 3, 4]], proof := .tail 57 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12038)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![4, 6, 3, 1, 5, 2], ![4, 3, 6, 0, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 1, 3, 0, 4]], proof := .tail 30 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12039)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![4, 6, 3, 1, 5, 2], ![4, 6, 3, 0, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 1, 0, 4]], proof := .tail 28 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12040)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 4, 3, 1, 5, 2], ![4, 3, 6, 0, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 1, 3, 4, 0]], proof := .tail 15 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12041)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 4, 3, 1, 5, 2], ![4, 6, 3, 0, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 6, 0, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 1, 4, 0]], proof := .tail 28 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12042)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 4, 3, 1, 5, 2], ![6, 4, 3, 0, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 6, 1, 0, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 4, 1, 0]], proof := .tail 56 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12043)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![4, 3, 6, 1, 5, 2], ![4, 3, 6, 0, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .tail 42 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12044)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![4, 6, 3, 1, 5, 2], ![4, 3, 6, 0, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 17 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12045)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![4, 6, 3, 1, 5, 2], ![4, 6, 3, 0, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 28 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12046)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![4, 6, 3, 1, 5, 2], ![4, 6, 3, 0, 5, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 55 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12047)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 4, 3, 1, 5, 2], ![4, 3, 6, 0, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 1, 3, 4, 0]], proof := .tail 12 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12048)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 4, 3, 1, 5, 2], ![4, 6, 3, 0, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 3, 1, 4, 0]], proof := .tail 28 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12049)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 4, 3, 1, 5, 2], ![4, 6, 3, 0, 5, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 1, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 2, 0, 1, 3, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 12 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12050)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 4, 3, 1, 5, 2], ![6, 4, 3, 0, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 6, 1, 0, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 3, 4, 1, 0]], proof := .tail 56 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12051)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 4, 3, 1, 5, 2], ![6, 4, 3, 0, 5, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 1, 0, 5], ![3, 2, 6, 1, 0, 5], ![6, 2, 0, 1, 3, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 56 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12052)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 4, 3, 1, 5, 2], ![6, 4, 3, 0, 5, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 1, 0, 5], ![3, 6, 2, 1, 0, 5], ![6, 2, 0, 1, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 36 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12053)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 4, 3, 1, 5, 2], ![6, 4, 3, 0, 5, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 1, 0, 5], ![6, 3, 2, 1, 0, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 47 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12054)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![4, 3, 5, 1, 2, 6], ![4, 3, 5, 0, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 0, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 61 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12055)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![4, 3, 5, 1, 2, 6], ![4, 3, 5, 0, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 0, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 26 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12056)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![4, 3, 5, 1, 2, 6], ![4, 3, 5, 0, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 1, 0, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 9 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12057)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![4, 3, 5, 1, 2, 6], ![4, 3, 5, 0, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 0, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 63 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12058)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![4, 3, 5, 1, 2, 6], ![4, 3, 5, 0, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 0, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 63 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12059)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![4, 3, 5, 1, 2, 6], ![4, 3, 5, 0, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 1, 0, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 63 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12060)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![4, 3, 5, 1, 6, 2], ![4, 3, 5, 0, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 0, 3, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 63 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12061)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![4, 3, 5, 1, 6, 2], ![4, 3, 5, 0, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 0, 3, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 63 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12062)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![4, 3, 5, 1, 6, 2], ![4, 3, 5, 0, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 1, 0, 6, 3, 4], ![2, 0, 1, 5, 3, 4]], proof := .tail 63 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12063)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![4, 3, 5, 6, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 0, 3, 4, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 52 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12064)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![4, 3, 5, 6, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 0, 3, 6, 4], ![2, 1, 0, 3, 5, 4]], proof := .tail 52 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12065)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![4, 3, 5, 6, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 1, 0, 6, 3, 4], ![2, 1, 0, 5, 3, 4]], proof := .tail 52 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12066)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![4, 3, 6, 5, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 1, 6, 0, 3, 4], ![2, 1, 5, 0, 3, 4]], proof := .tail 13 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12067)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![4, 3, 6, 5, 1, 2], ![4, 3, 6, 5, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 1, 0, 3, 4]], proof := .tail 53 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12068)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![4, 3, 6, 5, 1, 2], ![4, 3, 6, 5, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .tail 63 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12069)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![4, 6, 3, 5, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![2, 1, 6, 0, 3, 4], ![2, 1, 5, 3, 0, 4]], proof := .tail 66 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12070)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![4, 6, 3, 5, 1, 2], ![4, 3, 6, 5, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 1, 3, 0, 4]], proof := .tail 53 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12071)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![4, 6, 3, 5, 1, 2], ![4, 3, 6, 5, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 66 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12072)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![4, 6, 3, 5, 1, 2], ![4, 6, 3, 5, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 3, 1, 0, 4]], proof := .tail 33 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12073)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![4, 6, 3, 5, 1, 2], ![4, 6, 3, 5, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 33 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12074)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![4, 6, 3, 5, 1, 2], ![4, 6, 3, 5, 0, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 2, 1, 0, 3, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 65 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12075)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 4, 3, 5, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![2, 1, 6, 0, 3, 4], ![2, 1, 5, 3, 4, 0]], proof := .tail 38 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12076)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 4, 3, 5, 1, 2], ![4, 3, 6, 5, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 1, 3, 4, 0]], proof := .tail 53 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12077)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 4, 3, 5, 1, 2], ![4, 6, 3, 5, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 6, 0, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 3, 1, 4, 0]], proof := .tail 33 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12078)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 4, 3, 5, 1, 2], ![6, 4, 3, 5, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 6, 1, 0, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 3, 4, 1, 0]], proof := .tail 45 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12079)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 4, 3, 5, 1, 2], ![4, 3, 6, 5, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 1, 3, 4, 0]], proof := .tail 59 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12080)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 4, 3, 5, 1, 2], ![4, 6, 3, 5, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 3, 1, 4, 0]], proof := .tail 33 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12081)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 4, 3, 5, 1, 2], ![4, 6, 3, 5, 0, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 1, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 2, 1, 0, 3, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 65 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12082)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 4, 3, 5, 1, 2], ![6, 4, 3, 5, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 6, 1, 0, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 3, 4, 1, 0]], proof := .tail 45 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12083)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 4, 3, 5, 1, 2], ![6, 4, 3, 5, 0, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 1, 0, 5], ![3, 2, 6, 1, 0, 5], ![6, 2, 1, 0, 3, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 8 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12084)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 4, 3, 5, 1, 2], ![6, 4, 3, 5, 0, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 1, 0, 5], ![3, 6, 2, 1, 0, 5], ![6, 2, 1, 0, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 22 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12085)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 4, 3, 5, 1, 2], ![6, 4, 3, 5, 0, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 1, 0, 5], ![6, 3, 2, 1, 0, 5], ![6, 2, 1, 0, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 47 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12086)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![4, 5, 3, 1, 2, 6], ![4, 3, 5, 0, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 41 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12087)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![4, 5, 3, 1, 2, 6], ![4, 3, 5, 0, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 5 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12088)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![4, 5, 3, 1, 6, 2], ![4, 3, 5, 0, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 68 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12089)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![4, 5, 3, 1, 2, 6], ![4, 3, 5, 0, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 27 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12090)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![4, 5, 3, 1, 2, 6], ![4, 3, 5, 0, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 5 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12091)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![4, 5, 3, 1, 6, 2], ![4, 3, 5, 0, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 58 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12092)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![4, 5, 3, 6, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 69 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12093)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![4, 5, 3, 6, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![2, 1, 0, 3, 5, 4]], proof := .tail 69 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12094)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![4, 5, 6, 3, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![2, 1, 3, 0, 4, 5]], proof := .tail 18 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12095)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![4, 5, 6, 3, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![2, 1, 3, 0, 5, 4]], proof := .tail 18 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12096)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 2 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12097)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![2, 1, 6, 3, 0, 4], ![2, 1, 5, 3, 0, 4]], proof := .tail 44 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12098)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 3, 6, 5, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 1, 3, 0, 4]], proof := .tail 54 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12099)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 3, 6, 5, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 24 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12100)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 6, 3, 5, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 1, 5, 0], ![3, 2, 1, 0, 6, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 3, 1, 0, 4]], proof := .tail 23 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12101)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 6, 3, 5, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 1, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 16 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12102)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 6, 3, 5, 0, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 1, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 60 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12103)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 6, 0, 5], ![2, 1, 3, 6, 0, 4], ![2, 1, 3, 5, 4, 0]], proof := .tail 10 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12104)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![4, 3, 5, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 6, 0, 5], ![2, 1, 6, 3, 0, 4], ![2, 1, 5, 3, 4, 0]], proof := .tail 44 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12105)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![4, 3, 6, 5, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 6, 0, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 1, 3, 4, 0]], proof := .tail 54 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12106)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![4, 3, 6, 5, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 6, 0, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 1, 3, 4, 0]], proof := .tail 70 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12107)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![4, 6, 3, 5, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 1, 5, 0], ![3, 2, 1, 6, 0, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 3, 1, 4, 0]], proof := .tail 23 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12108)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![4, 6, 3, 5, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 1, 5, 0], ![3, 2, 1, 6, 0, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 3, 1, 4, 0]], proof := .tail 16 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12109)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![4, 6, 3, 5, 0, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 1, 5, 0], ![3, 2, 1, 6, 0, 5], ![6, 2, 1, 3, 0, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 60 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12110)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![6, 4, 3, 5, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 1, 5, 0], ![3, 2, 6, 1, 0, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 3, 4, 1, 0]], proof := .tail 23 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12111)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![6, 4, 3, 5, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 1, 5, 0], ![3, 2, 6, 1, 0, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 3, 4, 1, 0]], proof := .tail 16 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12112)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![6, 4, 3, 5, 0, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 1, 5, 0], ![3, 2, 6, 1, 0, 5], ![6, 2, 1, 3, 0, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 3 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12113)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![6, 4, 3, 5, 0, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 1, 5, 0], ![3, 6, 2, 1, 0, 5], ![6, 2, 1, 3, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 29 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12114)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![6, 4, 3, 5, 0, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 1, 5, 0], ![6, 3, 2, 1, 0, 5], ![6, 2, 1, 3, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 21 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12115)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![4, 5, 3, 1, 2, 6], ![4, 5, 3, 0, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 46 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12116)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![4, 5, 3, 1, 2, 6], ![4, 5, 3, 0, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 62 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12117)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![4, 5, 3, 1, 6, 2], ![4, 5, 3, 0, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 62 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12118)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![4, 5, 3, 1, 2, 6], ![4, 5, 3, 0, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 6 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12119)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![4, 5, 3, 1, 2, 6], ![4, 5, 3, 0, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 62 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12120)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![4, 5, 3, 1, 6, 2], ![4, 5, 3, 0, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 62 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12121)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![4, 5, 3, 6, 1, 2], ![4, 5, 3, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 51 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12122)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![4, 5, 3, 6, 1, 2], ![4, 5, 3, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 1, 0, 3, 5, 4]], proof := .tail 51 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12123)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![4, 5, 6, 3, 1, 2], ![4, 5, 3, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 1, 6, 0], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 1, 3, 0, 4, 5]], proof := .tail 25 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12124)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![4, 5, 6, 3, 1, 2], ![4, 5, 3, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 1, 3, 0, 5, 4]], proof := .tail 25 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12125)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 5, 3, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 64 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12126)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![4, 5, 6, 3, 1, 2], ![4, 5, 6, 3, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 1, 0], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 35 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12127)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![4, 5, 6, 3, 1, 2], ![4, 5, 6, 3, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 3, 1, 0, 5, 4]], proof := .tail 35 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12128)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 5, 6, 3, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![2, 3, 1, 5, 0, 4]], proof := .tail 64 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12129)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 6, 5, 3, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 6, 1, 0, 4], ![2, 3, 5, 1, 0, 4]], proof := .tail 1 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12130)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 6, 5, 3, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 1, 0], ![3, 2, 1, 0, 6, 5], ![2, 6, 3, 1, 0, 4], ![2, 5, 3, 1, 0, 4]], proof := .tail 34 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12131)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 6, 5, 3, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 1, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 3, 1, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 62 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12132)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 6, 5, 3, 0, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 1, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 3, 1, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 7 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12133)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![4, 5, 3, 6, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 1, 6, 0], ![3, 2, 1, 6, 0, 5], ![2, 3, 1, 6, 0, 4], ![2, 1, 3, 5, 4, 0]], proof := .tail 11 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12134)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![4, 5, 6, 3, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 1, 0], ![3, 2, 1, 6, 0, 5], ![2, 3, 1, 6, 0, 4], ![2, 3, 1, 5, 4, 0]], proof := .tail 11 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12135)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![4, 6, 5, 3, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 1, 0], ![3, 2, 1, 6, 0, 5], ![2, 3, 6, 1, 0, 4], ![2, 3, 5, 1, 4, 0]], proof := .tail 1 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12136)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![4, 6, 5, 3, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 1, 0], ![3, 2, 1, 6, 0, 5], ![2, 6, 3, 1, 0, 4], ![2, 5, 3, 1, 4, 0]], proof := .tail 34 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12137)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![4, 6, 5, 3, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 1, 0], ![3, 2, 1, 6, 0, 5], ![6, 2, 3, 1, 0, 4], ![5, 2, 3, 1, 4, 0]], proof := .tail 62 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12138)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![4, 6, 5, 3, 0, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 1, 0], ![3, 2, 1, 6, 0, 5], ![6, 2, 3, 1, 0, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 7 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12139)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![6, 4, 5, 3, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 1, 0], ![3, 2, 6, 1, 0, 5], ![2, 3, 6, 1, 0, 4], ![2, 3, 5, 4, 1, 0]], proof := .tail 14 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12140)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![6, 4, 5, 3, 0, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 1, 0], ![3, 2, 6, 1, 0, 5], ![2, 6, 3, 1, 0, 4], ![2, 5, 3, 4, 1, 0]], proof := .tail 31 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12141)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![6, 4, 5, 3, 0, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 1, 0], ![3, 2, 6, 1, 0, 5], ![6, 2, 3, 1, 0, 4], ![5, 2, 3, 4, 1, 0]], proof := .tail 31 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12142)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![6, 4, 5, 3, 0, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 1, 0], ![3, 2, 6, 1, 0, 5], ![6, 2, 3, 1, 0, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 20 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12143)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![6, 4, 5, 3, 0, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 5, 1, 0], ![3, 6, 2, 1, 0, 5], ![6, 2, 3, 1, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 49 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12144)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 4, 5, 3, 1, 2], ![6, 4, 5, 3, 0, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 5, 1, 0], ![6, 3, 2, 1, 0, 5], ![6, 2, 3, 1, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 49 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12145)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![4, 5, 3, 1, 2, 6], ![4, 5, 3, 0, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 50 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12146)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![4, 5, 3, 1, 2, 6], ![4, 5, 3, 0, 6, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 37 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12147)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![4, 5, 3, 1, 6, 2], ![4, 5, 3, 0, 6, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 37 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12148)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![4, 5, 3, 1, 2, 6], ![4, 5, 3, 0, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 4 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12149)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![4, 5, 3, 1, 2, 6], ![4, 5, 3, 0, 6, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 37 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12150)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![4, 5, 3, 1, 6, 2], ![4, 5, 3, 0, 6, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 37 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12151)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![4, 5, 3, 6, 1, 2], ![4, 5, 3, 6, 0, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 67 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12152)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![4, 5, 3, 6, 1, 2], ![4, 5, 3, 6, 0, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![2, 1, 0, 3, 5, 4]], proof := .tail 67 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12153)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![4, 5, 6, 3, 1, 2], ![4, 5, 3, 6, 0, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 1, 6, 0], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![2, 1, 3, 0, 4, 5]], proof := .tail 48 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12154)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![4, 5, 6, 3, 1, 2], ![4, 5, 3, 6, 0, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![2, 1, 3, 0, 5, 4]], proof := .tail 48 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12155)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 5, 3, 6, 0, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 39 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12156)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![4, 5, 6, 3, 1, 2], ![4, 5, 6, 3, 0, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 1, 0], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 28 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12157)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![4, 5, 6, 3, 1, 2], ![4, 5, 6, 3, 0, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![2, 3, 1, 0, 5, 4]], proof := .tail 28 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12158)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![4, 6, 5, 3, 1, 2], ![4, 5, 6, 3, 0, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![2, 3, 1, 5, 0, 4]], proof := .tail 28 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12159)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (12032 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 12032 ≤ id.val) (hhigh : id.val < 12160) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 12032)) = true := by
  let j : Fin 128 := ⟨id.val - 12032, by omega⟩
  have hsum : 12032 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (12032 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard094
