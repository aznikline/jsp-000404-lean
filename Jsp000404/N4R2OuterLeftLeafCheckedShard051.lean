import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard051
open N4R2OuterLeftReplay

-- Cycle fingerprint 02f5d9b387d7588304edf3fb918a29e4065578475b9b78e3709d7ac9fdb15bc2.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 5]
    constant := ![0, -2, 0, 0, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, true, true, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 1 2, .triangle 5 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 17 2]

-- Cycle fingerprint 0757cebba9acdc8def455ec375e60d025abac4d38f4f5c8e45b3d09df6c1fb15.
def localCycle00001 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 0767da3a35232a7b4aba5c5346c548d5d7230e347a3e278333a47fe7fa539018.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint 081f8289bcf4e7c8be1c89d91a107f21352ce699d0d7aa26befb48d8258aa0df.
def localCycle00003 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 08366d07965c144b2743d5c3801245ae666bd92f42111b4ae88237185e306984.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 5]
    constant := ![0, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 10 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 3 2]

-- Cycle fingerprint 098dd2339fe13dc5593f3a2b04501e10363608d0a2eefb18e7c66a43642b2c43.
def localCycle00005 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 5]
    constant := ![-2, 0, 0, 0, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, true, false, false, true, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 17 2]

-- Cycle fingerprint 09968ec055105195a5810b9bfccd60dbd2f6c253d1c11d3d437b3b54510ee340.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 33 2, .corridorLower 3 6]

-- Cycle fingerprint 0a319a2211eee0633c3d2d41dbd1dddae8f3d007628f2d932ddcb76a8573ee7d.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, 0, -2, 0, 0, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 20 2, .triangle 24 2, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 0a5356e1e572cf5ef7b932698acda976f06d96bada331b389e44f0ffa8cfd1e6.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 0a71ea6229e8e4bb76ce7ef4aad5a3c76deddb430001428ae6f9444ac8b97973.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3]
    constant := ![-1, -1, 0, 3, -3, 0, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true] }
  origin := ![.triangle 25 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 2, .triangle 8 1, .triangle 27 1]

-- Cycle fingerprint 0be961b25cc229563c6cba0056560d1842fcb7bc0b385d13f18362d915b703a1.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0c181225aed25c675e2318050830c6d33b6076203caf13cc00acfee841c02701.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, 0, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 0d3f02cfb69e43bc49baa7f2e5df4e20bb047ee50efe90a5e00b9e1651447c7d.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 0ddbeb6499c5818892c00d9586d30c84b80faf5ae620a0b81b56a4e583aa5a1f.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 2, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 0eebfc14fbbb120f9662f12243d855d9fbec5f645ccdf7e509fb7f6f2255b0d7.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, 0, -2, 0, 0, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 21 2, .triangle 24 1, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 0f87001adf4326208981a4fe043729283fab5678a4909bb15378f78eb762efa9.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 0feb7292c8d55f1b03999055d711ba50353b4a5ade79d8ac50087e797468c473.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 105997eedb64e5947c9b7bbf00b1e671fe3faa285a6a26fa78fbf655f6391350.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 10abb589bd80370de9981f2fbd46997f2247a261d66e2dec72cc1ebe87f510fa.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 12fa56be13f68eb328f5084ad20967ea6fc0061be414dcef33d9be1d0879302d.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 1477633cd0b5888ea104cf4c852e5d8ac0c1a7d1f550f9d3324e9607554f662d.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 19 2, .triangle 23 2, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 1588d52b1999bd7055c020fe7ff2f46bf0f6114d51a2549f4a15db5147ec65d5.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint 15d0a957a75030efb2cc861e955ccfc32da736704158f85b1a785812f48cf3fb.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 1669545606e7047266e84bb34f3e3622b90d94c84a85f79c07372b91781c05b6.
def localCycle00023 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 21 2, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 168c88362af97369aa4600d85946f30e03e34035e28a73622fec181266709b88.
def localCycle00024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 2]

-- Cycle fingerprint 174d9cdc31681b43f086779018c1a89829f8e9f198eae8fae92119993c8a47c7.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 1836f008d953903c1fa8565934faef462e52bb159954216344fec7d1dc065f0b.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 5, .distance 2 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .zero, .theta 1, .distance 1 2, .distance 1 5]
    constant := ![0, 0, -1, -1, 0, 0, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 7 1, .triangle 30 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaLower 3, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 18e0c03e6f53e05afe065001eb70b880c8923092e440ec1ea3e0cfc7fc2f4c34.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 24 2, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 1e292d738ec7e970077a30e3ea1349e5812f235e9a61b3e2c3e519b4463643d0.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 1e5f2095733f130b5adfa8fbb96bab9bcd533025ced0e1ae18877284eb47c5f4.
def localCycle00029 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 1f94d85109995dfc251909d375daaa9cd6ee445f95e5ff7830bea7421ce7e85f.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3]
    constant := ![-1, 3, 0, 0, -3, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 27 0]

-- Cycle fingerprint 1faf8182d1e9e37296d72792498b19517d7a65af86c7a0f506da01de7f9587be.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 2185159056c47f14e3a18280ec92928991f887893e4d56b1df9c9e34e15a4c9b.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 21ac3e6cd98b936187ff4d01e107ed3b66f733bf58353ac89ecdb632701333e8.
def localCycle00033 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 21c8f6f86e326258fb211c36a59597dea0f34028cc2dbc805e06eabc893aced9.
def localCycle00034 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 25700aad084d72a23188b11e5d3cd6894afede9f6f75375e05a0eb484ae0a613.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -2, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapLower 1 4, .triangle 20 1]

-- Cycle fingerprint 261cd39b44c0a7133dd5d8a925d290af9cfa074473edda6df2bb2c6562652bf3.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 26c89fed1f5bd8836a944e070c79b984a16efc235e898ca25ad5871719d9bef8.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 26de5922f024482c18d38f12881065bae586345ec0385dad86ae5999f790b2b7.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 273bcf25ec29f5625804bb99b446008373590371664ced522b8f438b70ba9ba2.
def localCycle00039 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 27a0c4df6de3fe7178b889cb6ef718100caff89ec2485c87c5bee42cf438ad09.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 1, .triangle 20 1, .triangle 1 0]

-- Cycle fingerprint 29daeec6a434b50fd23e66b86ef70c319d12f25ee457ce2bbd6cea90c9024482.
def localCycle00041 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .theta 4, .theta 3, .distance 1 3]
    constant := ![-3, -2, 0, 3]
    coefficient := ![0, -1, 0, 1]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 4, .gapUpper 4 6, .thetaNext 3, .corridorUpper 1 3]

-- Cycle fingerprint 2b1a3202889fb47008b8ff86a7361dc2b3a236ec22f7eb629d8360c201825c56.
def localCycle00042 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 2ba6b65fbbd7e38adefb87662ec7ac0a8e1ffcb0fdc915a002d6c5ad15327ce7.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 22 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 2bbdafa30bc5eef8c95ed9be279a6cb8d267ec949f3fda9f1d79048ac78373ff.
def localCycle00044 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .theta 4, .theta 3, .distance 1 3]
    constant := ![-2, -2, 0, 3]
    coefficient := ![0, -1, 0, 1]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 4, .gapUpper 4 6, .thetaNext 3, .corridorUpper 1 3]

-- Cycle fingerprint 2bcf93967e60d73ad97b597244717b6e170ed985796bcb401728562f06193e57.
def localCycle00045 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 24 2, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 2be49b43af0eb66477303b2a63ee0aafbd6683730bce846239629eeee359ca68.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 2ce84c5bc39c79b6f482e7689d8a8945d7890021b927c9a2787225a2a9d4d5bb.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 11 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 20 2, .gapLower 1 3, .triangle 4 2]

-- Cycle fingerprint 2e23d92b9c437588bc8e2450fefc1582adc9ad5d036de6078ce71c03026c771a.
def localCycle00048 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 24 2, .gapLower 1 4, .triangle 20 1]

-- Cycle fingerprint 2f44d16be0722942992111c5d8bc198d70004c99d62c1bdf3d2bbf4823cb1182.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 2fd232bdea3fb67c2f1d67eae70e1ce1fe6d521993f3550ccca001e644d58894.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 11 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 2, .gapLower 1 3, .triangle 4 2]

-- Cycle fingerprint 3051904ed865f88664cd15a117b8e40857cd01028e0e9f86b906dbcb287026f3.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 305247308ec6a8edb21453db032726cdfcf5e57ae4498566a64f3e48c73bd670.
def localCycle00052 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 6]
    constant := ![-2, -2, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 19 2, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 6 3]

-- Cycle fingerprint 30b0c90b3a7c1db76ca7e51c6e285c8b30d0960565d59e993c76536113314512.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 31bd10c47389bbac826cb4b9a488a3bf2bc2bfa983bba20d0e73651e715cd507.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 324611cbabad0b62ed398224aa7b6381813917399a5be94f5a2cb53ecb5f3f0a.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 32bb7db62c81ca3215628c1fbfc7e16dd50bfeca100bc551a8bbd3438ab642a1.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Cycle fingerprint 32d84064cd4a38103b0bf77eefd7dee294cb59c7e8546026409225312c5ffc4e.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 330a4c5cefdd3078628636839b78d5459ed607bc9a7610e52fbfbbca5bfdc01d.
def localCycle00058 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 3318a6459408e0c837d7ab9272e4b103d7d979c20f31a681098fe595e23b282a.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 348699b46fbd3908b128369d1b60d20970eb2262f78198f281e888290b0c47bd.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 34a9ed0d4b385c77a0b612d4f69ca4e70c6d7ac7f84a6fe5af75de00de1e6aef.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 35b326c7288bf757af1fa6bcb22960e5ea5e147cd1647127d622cf5b460e4b1d.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 3699680e90c80a615da68fa38df1df94137241366f07ffe9eaa36b438a0efd88.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 370a04767305ec748e68a0acb3d40575790c79ea987cd892cedaa94b493c8381.
def localCycle00064 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 27 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 3a18b8b65be2b0655f33d6d6fab02c4ac489fc1b7cdbb836456b66c5cd97424c.
def localCycle00065 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 3a71a1f161a511d0086814472614f26ac7c64e44fbf6fb1dbd018c3ef0f5dfd7.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 34 1, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 3efe0e5ec6eb7c28778a059ae0ba842828c440df148e3f2160b9cce5619e7dff.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 3, .triangle 24 1, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 407ff449cd90ba678a382357b557b526cfa3ddc411a279702247901c2fffd9fe.
def localCycle00068 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 32 0, .triangle 29 2, .gapUpper 2 4]

-- Cycle fingerprint 41a718033d48fd72cf0f2a79e344169e0c76a673341f26a411f1601187469bc4.
def localCycle00069 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 43cb5dbf73aa0ba367442c801e9020f69326629dd06f0ffb7a2e00c56c8087c2.
def localCycle00070 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 5]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 5 4, .triangle 20 0, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 442245a29fcce4d61c99015c01574b5e92276d3a4589f453f356d63c9527fdc6.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 44895357066980f36fde9005f7280c02c7485806704659c9010872dfc9f9f5be.
def localCycle00072 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint 44e1eabea239e7638e56ceef1648a3f5004c5efb8ed5210de9666ebb89ce1d3e.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 45157a4f1288c9bbb58b27f68986c7710f4e3817b74cf880c107a0d2adc3cfdb.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 2 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 45697806ab390b2e4da3db53bb0649cd09e1f0a6649dc528ea32ad1c04a7fb87.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 6 4, .gapLower 1 3, .triangle 22 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0]

-- Cycle fingerprint 45dfcb1c2182e81b506fd3b87c44469e9fee5860fd56f6e199ced28827d3a2f5.
def localCycle00076 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 46900d87a35f1b53fb2c704f47fbb6f7eee9fcec4950bb57adb9694503bcc0f5.
def localCycle00077 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 477ce304bb2c35d3613c6d671daccad3b5dbff87719aece56e3c971ccf0732f9.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .triangle 23 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 480e0c394b9eb1f3de08bfe9d3b3d5c41ca6e33cd4db0d2ac3461bf1cba83235.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, -2, 0, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint 487f0e9b51be787669b8aa3f63a896bf2581f10ba2ad7157b408b999ec32f282.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 21 1, .triangle 1 0, .gapLower 1 0]

-- Cycle fingerprint 490c04ff3dcb91dfd5a653e4cf1dc36b1e043c787c67e4e0e86859a86752dfa6.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 2 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint 4a0ad45d7f8e00ceb7a85346467493ef4e955cd76f0531e6c23a08693859c2ed.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 4acdeefd550114d31de9d6c36f29589fd173ac80a91e771ffcf2442579706cdb.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 32 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 4aebf36f2b8e0f16f8aaa6733589c8fe820e60e7b33facb0dec6aec86c6630e4.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 4b0f51a3dbca609f0629a09244d6307f959ac04a3bef3c83740b6f5969503175.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 4 6, .theta 6, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -2, 2, -2, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, -1, 0, 1, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .gapLower 1 2, .gapUpper 4 4, .gapUpper 6 6, .thetaNext 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint 4b66f6bf8d05091d2037b24fb323d829297a1bf4f6d35fc95da53d8c00f97994.
def localCycle00086 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 3 5, .distance 1 5, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 5 4, .triangle 20 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 4d1a589828b26f8f67e92c8edef4129b1299a3fb80d2f5c88dbee4ef9a8b91d8.
def localCycle00087 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 4e08e0893f423e2215e326026be327ec6d5921b71685e342395353c99587a7c3.
def localCycle00088 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .gapLower 6 3, .gapLower 1 4, .triangle 20 1]

-- Cycle fingerprint 4e3455f54b088113e388fccb71b857ae3fec72fb5777b03a7531e0b30ede0531.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 4e578450ea348793da545a47d2a90efa6b6906f5e566c6fa017d5c9a28e04d03.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 5]
    constant := ![0, -1, -1, 3, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 31 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 33 1]

-- Cycle fingerprint 4ec4e043a410186edc6e26733f7a0834229de358d2c081d61d0ad3772f0736dc.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 4f70487eab98dd3f4f013d1ba107282f088e04452d8dda861ec29b3c144b8464.
def localCycle00092 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-3, 0, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 505afba75ebad145be2158df367dcf66af0a037f0f562d77fa296826dbd39121.
def localCycle00093 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 3 5, .distance 1 5, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 5 4, .gapLower 5 3, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 50d643bc2d515e356bb58a70ba9ff2772d6aa66cf742872c2bf8d5dd428bc3f8.
def localCycle00094 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true] }
  origin := ![.triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 4]

-- Cycle fingerprint 5194e5a1c819c71055ac6ebf27d09e77cb0ade5deee65955cdda51e4703700cc.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 51c5b1b0a4c204c401b936f9f1585dc36c7012bd945ffd28f3f2ceed8b3fc9f0.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 5, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![0, -3, 0, 0, 0, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, true, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 3 2, .triangle 7 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 52921440addfaf86e8b37e2a40f12ad85c96991e3fdae965b39abdadff4d53ee.
def localCycle00097 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 52d9cef4e58816fe425144dc59fc8fd67090646f0c5892545f065736bff08aff.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 53afce190c91dde3d08b7264afaf30c1c49087299adee4a60951107842644fd0.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![0, -3, 0, 0, 0, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, true, false, false, true, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 53dc273ed659a6f6e0017bca93d58c3c162036ee864923638e76ee608bf17930.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 33 1, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 5437339e134310b6090b47e9e7eb2bc33fa0a51dbc88e2c4b178b526878e5908.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 55934910b99eea73eaeefd5b2ed65129696baa6ff551b09723a6da224e3a9129.
def localCycle00102 : Cycle where
  length := 3
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .theta 2]
    constant := ![0, 1, -2]
    coefficient := ![0, 1, -1]
    strict := ![true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapUpper 2 6]

-- Cycle fingerprint 55debf33fb7a661517d1815add01498962344dbdaab2c31ecd6209c961a564c0.
def localCycle00103 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 2 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 56bac1e5418536e6ed8ab2aed7051e7ee32b8d5b22eff10d975f618bc7459ab9.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5989a94c01118eccc4dfc095fcb449ea2b0829adee6d2f5515a145ae7a962a1f.
def localCycle00105 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 59a0b10ca0a19becf0a7b61f2937e4c2d41559165c4aa5eea62e0d8c6332a6d7.
def localCycle00106 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 5b653f314b8cdfdf5b7a14a2e4ade751829bdb6d18c2fe4fae6a4e80f5004a6e.
def localCycle00107 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 5bdb6ad96d542796757f5788fe28291c78ffbb13358b51d400799d625cb31d2b.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 3]
    constant := ![-1, -1, 0, 0, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 7 0, .triangle 26 1]

-- Cycle fingerprint 5ca896964e3f70182a9cd49811c227b10757cdb8ef8c4bac93f74f526a87c906.
def localCycle00109 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5d3469670e22636377b20443ea8a0ee092ce9ddf317e79b6e2e22b30f5b61e18.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 20 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 5e2abb2547929e564bbae6b9c67be8db24d4400e09296fb7ef897e7e4e215da0.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .triangle 14 0, .triangle 30 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5ef1b29a5cc28fe9a352fcac32befaaa43b95d224b95e4d3d05e50f090334e1e.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 20 1, .triangle 1 0, .gapLower 1 0]

-- Cycle fingerprint 5f2394fba284e064ccfd0ed51b7280915ae36f1a84f01ad71fab2b5e38713e3a.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5]
    constant := ![-1, 0, -1, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5, .corridorUpper 1 3, .triangle 19 2, .triangle 22 2]

-- Cycle fingerprint 5fa691434e96c4a013f3b6783c11b509cc62e00973af7b2a4372f7f27e0e03f9.
def localCycle00114 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 5fe643747ad66ead08adda477ade93c7976aaadce7576cbeaeae5dfb389202c0.
def localCycle00115 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 60b6a069ef79a8a61dc318c7968b105cdf07c826ea0639c419d6bb6a34f24819.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 60c7a55d1939383b8d61c5bc77fa0a2c5c7360119ba8d4e95db4d5ae8cc5c88f.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .zero, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![0, 0, 0, 0, -1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 8 1, .triangle 30 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 61ebacee2fe9af5ade61403aa7b875ebf97208bdf2a11fc0de025cfbd59b0c70.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 61f684c3439a4460b6233312ddeb731b96f696e8f1db822237572dda674cc0c9.
def localCycle00119 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 61fa162dc5a3752fa494de96319eb100cd3a877196a87dc4e91292baac82de0a.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -2, 0, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 62ec7b389d18c33d3693f87e11b579e020091c3082e84391afb44889467c78c3.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 652d480322754e47a65974d882d62b0af1626479a3559bc25cec0cbed8574193.
def localCycle00122 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, 0, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true] }
  origin := ![.triangle 33 0, .triangle 24 0, .triangle 20 1, .triangle 19 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 65de18ae97778e4aeeeefa70ee8ae18c43a4bbd6ff104cc2608c7cb7b18e939f.
def localCycle00123 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 66131489cdd83483565fda9b4e775c15f30d1a3611e89ae04d039d861a6b8a1d.
def localCycle00124 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 67f5c75a246e42dc1668f36a26fb46c8f71608eb48703671e360aa1c1cec22fb.
def localCycle00125 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 5 4, .triangle 20 0]

-- Cycle fingerprint 6948d6b502ecaf80c0af8ae6d97aa71e378653989bc1e8b17c440881956c5552.
def localCycle00126 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 3 5, .distance 2 3, .theta 3, .distance 1 3, .distance 1 5, .distance 0 5]
    constant := ![0, -1, 0, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 10 1, .triangle 26 0, .gapLower 3 0, .corridorUpper 1 3, .gapLower 1 4, .triangle 3 2]

-- Cycle fingerprint 694f94acbb1b08719163b26a51f733584e4dc275cf0b76f2109694cde7efdca2.
def localCycle00127 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 6a01ded6af86d7c16e13ae59ba25b63caf831d3d74cdee558a52fbbbbd1f432b.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![-1, -3, 0, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 20 0]

-- Cycle fingerprint 6b2b592a12da90b1a8409d0f8c65016203d7d47c37dbd08cc1b0c80003d9ce36.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 6c3d81da5d3e5e910a9a1168f4b95d504bf3c4fb8a18501d7b5efdbddffa2136.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6c5e7887d62a530fda1e637ede4727b69ae10951db4a97b14fa48ec7141b49b9.
def localCycle00131 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 2, .gapUpper 2 4]

-- Cycle fingerprint 6c822ba1657deebd53e14488d2390387d5b9994c99345b33a60dcecf22b070e9.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 1 2, .triangle 5 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 6e4ff82922d808740b88ac15fe306a601688bcb1297868b98a4ef8f24c93bcc1.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Cycle fingerprint 6e8c5f99c6f77869148f214811408856f39a2ece2180d7b1e59c399e5a55c466.
def localCycle00134 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 22 2]

-- Cycle fingerprint 7121186b334f935417faceb37323a21ef799e30ff2a2358a2c638b455fb80289.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 23 2, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 71fbe89b22d9f51c33c26894e2ca9c1b1d0063d1951a60d6b24e99d455ee785a.
def localCycle00136 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint 7378d69ee4fa91de457a494e1956b9848f25adc06042602a0f931fbe313c101d.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 73c48962ed2a8dab75ca0a7f87cf9e8a0ffaace6151663164c79a1ee797c6668.
def localCycle00138 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 74094a6bdc5a3374df4bbc6b89789447143c00116c99b2fd34113ecf5b4ced97.
def localCycle00139 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 75b85dc521f011778deae430dc259c6482f636a4f7c2ebd086dc352e50cc88b2.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 76174a6fd7524be8ec8fbf5ff5d146737fe60f4f9b4dfd5bf8b15a09f8691fd4.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 76b8e955ea2e25692866305fc911888685828bfdf86de4fb854c1f7ef0fb9a4a.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![0, -2, -2, 0, 0, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .gapLower 1 3, .triangle 1 2, .triangle 5 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 76de560132522c3835dcc53420feaf609bc7773c347a42870cde82476c6ced05.
def localCycle00143 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 7730149eb2ef3300b23bc7a15d8838bf4e256e8e5db9ece57d2cf78254274467.
def localCycle00144 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint 78b53964f499d845b8cf168190bfc023fe1e4b5880473f00b105cc9586f2dbe0.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5]
    constant := ![0, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 10 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 21 2, .gapLower 1 3, .triangle 3 2]

-- Cycle fingerprint 794623e23f7876d2cea9b398baec81a95af9e03fc49512ce49b7533ca585e5b6.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 7a5c39c3dd6aef6fe51c65626ee4e4f9f13eb0f1d89dc8c3166e5bc9ef6536d6.
def localCycle00147 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 7c1dcbb4c62c2dd0e36d608ce910ced4f115343e21c3f48c26650e809c708c0c.
def localCycle00148 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 2 0]

-- Cycle fingerprint 7de4036f0c269dee184080510c6bf9b4eebdc868f743f5e454e3f5022eedbe7d.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 3, .triangle 1 2, .triangle 5 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 7e0d0827de0844efa56059bb163c4edb32a715aa8b10e183a5d88ddda98d8815.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -2, 0, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 3, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 814f82613e1410b98b80c6ae68912012855d52ae3425dd2052edcbe0b091ec4a.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -2, -2, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .gapLower 1 4, .gapLower 1 3, .triangle 2 2, .triangle 9 1, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 81974a403129ad27af7c47d16310418185fe507689c8dfb159286184eb80a85c.
def localCycle00152 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 8331d50aadc88e0840704d0bf82e86989c0a1c0653f54bf8fef7dc5bc1bb271c.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 20 2, .triangle 24 2, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 842dd7fbc0e9b2fdaafb263455ffd671cbfb59c71a24f3bba60a3a6580b44fd0.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 849a9e79983087c0d5e340cb2b86cbe141794e6f0e910bd99e43f50d64130b8a.
def localCycle00155 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![0, -2, -2, 0, 0, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false, true, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 1 2, .triangle 5 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 84fb570426df36efc19f1d04d6c3b55b1d702b84d4cef81f0cfe9a94d5fe5b14.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 85bdf68d411fbc7523c4c8c92b8337df134025de4b3ad2869074feb0aba4d7b7.
def localCycle00157 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 4, .triangle 2 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 88e98ddfd0a4d68923feb8498691da644c073084046190fce9ddeb9e0cc38d88.
def localCycle00158 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![-2, 0, 0, 3, -2, -2]
    coefficient := ![-1, 0, 0, 1, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.gapUpper 4 6, .thetaNext 3, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 8b83b7fb073b49e853f02e89113ddfbf2c6e4480bb61893bc9893179cd4cf27f.
def localCycle00159 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 6, .distance 3 6, .distance 2 3, .theta 3, .distance 1 3, .distance 1 6, .distance 0 6]
    constant := ![0, -1, 0, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 11 1, .triangle 27 0, .gapLower 3 0, .corridorUpper 1 3, .gapLower 1 4, .triangle 4 2]

-- Cycle fingerprint 8be8512be76e804bbdb00495e7a2a2bc18c600b455eb4acaa7fee1a4b31c2230.
def localCycle00160 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, 0, -2, 0, 0, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 19 2, .triangle 23 2, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 8d787f3e36991c17bc0094c52b4abd13a6507eaaba3e7cf913e30e6b3915a273.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -1, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 33 1, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 8da41f4f11540574042fe14507bf0e3ffdcf569039a4eedd1790d4d560387883.
def localCycle00162 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 906271ff6ba68fa2799dc2ee6bab68cf001ce2de9bf29f3f2629ac07fdb85819.
def localCycle00163 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 9089fe31e3200687b39de97ec4ea764a240a38b2f1942251e816c63ba6971e54.
def localCycle00164 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 92f4b1d96f789d81ef644eeb136187c4bfc3bd2c91d0857a5c8ccd07370edfc2.
def localCycle00165 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5]
    constant := ![0, -1, -1, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 5 2, .triangle 10 0]

-- Cycle fingerprint 938721c4c4169e22f806348777effc4e17bea00acbb3d3963d6140d1e684e116.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 93f52cfd6e419ea9493b8f4ee9140a05ec12569c09067cbdb54ac4903542cf72.
def localCycle00167 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 4]

-- Cycle fingerprint 999132078f6144fbf5600f0551487497c5354bd86b6c6612539fb17ec22f2a21.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6]
    constant := ![-1, -1, 3, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint a000e4fda97fb1563d64c470df9af88ca664e44daf250532ca302dc3160cb8a5.
def localCycle00169 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 24 0, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint a0835de4c7fcc3651c7231293ed42ddff5d3508f2ec54448b7840d04e8b2ba31.
def localCycle00170 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint a23d16404afef87b817464e44710b90c26d00d4f9ee04703c966896a05bcb20f.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint a26b4811d0add84c90cd58e04100a7f203f4873a2d5f3bd71cd8ffc5cb0475d1.
def localCycle00172 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint a28742618c9c804a142e4685137005388fb1e731685a92f0b61f0de1151188a6.
def localCycle00173 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint a2eff47b36734f173eee0156d90208f98f6e7c5967a5708c2eedeccc715eb65a.
def localCycle00174 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a513a8e97c899b24a11b9ab07b741875a6de054bd008310b2cff1d2b81464eb6.
def localCycle00175 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint a5f938ce20466ac4d8c8187a4fbce701de71657f519c0afebbd9fbb29db570d4.
def localCycle00176 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint a8dd894850e1c56d10d385759626285ae9cb7a2d8a1e37b861a4aaf0468c265c.
def localCycle00177 : Cycle where
  length := 6
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6]
    constant := ![0, -1, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 6 4, .triangle 24 0, .gapLower 1 3, .triangle 19 2, .gapUpper 4 4, .gapLower 6 5]

-- Cycle fingerprint a9838ea1ac49fcbdd560b7ae56493dfcd04129e562a50ecfc30f48fb65e3c2e8.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 32 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 11 0]

-- Cycle fingerprint a9c360edebc7b9912b91efa8b1a636eb7eba923433f008a04e420fddf0b9cca0.
def localCycle00179 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 20 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint aa158225cdb4a78d84c3bdf9a6ee5b200a054da9d17f3ec1820660ab78e71008.
def localCycle00180 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint ab656db88cabfdb807624b02d04a6cd558b723cbf91ae0e0289e84eddf86f27a.
def localCycle00181 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint abc5ec9299306bf114e86669cfd136254219edcdb924ce3125636cd81090ae06.
def localCycle00182 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint acfcc20dc204bfed777ca76c7c679841ea359aadf50a82a3bddb3b24a8ccb159.
def localCycle00183 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true] }
  origin := ![.triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 4]

-- Cycle fingerprint ad2676ea14f30e356ce270f888bdbe1b9ad8efe7458505bd5e7c01a23e2fb02d.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint b0d02a1bca287c8a328e603d9370b992bebcf04b6545925110905c26974f9d6f.
def localCycle00185 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 5, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 3 2, .triangle 7 1, .triangle 26 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint b1e88e7e8c1647ee2703feed8a65eadac5bc7f062bf04271cb5d7dbcf66ef353.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 3 5]
    constant := ![0, -1, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 10 0]

-- Cycle fingerprint b574c14d5d0cd15d077750322171befec1c55da7f5d56509d369e0d143b4cb5b.
def localCycle00187 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 5, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![-2, 0, 0, 0, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, true, false, false, true, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 3 2, .triangle 7 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 18 2]

-- Cycle fingerprint b6522e5d282c4645a8ec86511fe48ee3139e5191a17dc7d99a6f4d7c066ef4f0.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 32 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 5 2, .triangle 11 0]

-- Cycle fingerprint b6aa56922b7b7c0c695d420a20b0dffd924cf3a239edce2395b3bbe0fc3f8d8e.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint b845239c0af2fc8ef043ab03fee228190fda476f3981f6d4358d024c127618b6.
def localCycle00190 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 3 5, .distance 1 5, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 5 4, .triangle 20 2, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint b90faba7513d3d628101fa0943cb471acc68430c47e56acc2cca1bd074a86e7b.
def localCycle00191 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint ba4863ef725062cf13ff783422ed66beac37a7b21bef2a434ac6e3fe757a7a14.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4]
    constant := ![0, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 9 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 21 2, .gapLower 1 3, .triangle 2 2]

-- Cycle fingerprint ba62ccac943ebbe1a96fd5fd161f937b9e6aa9c9871d1b39c88e2d3d272e6a37.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5]
    constant := ![-1, -1, 3, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 2, .triangle 10 1]

-- Cycle fingerprint bbfd00ec8957c923f274f07f0b17e2050b4cb8a45184955c2301a3c90c8bfbd4.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint be04e84f63ba552a5dac37c6d99212bee39271da9842126a5b4e2512746adc11.
def localCycle00195 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint beac32d9aa135a9b75bad75fc4f6562f705019171ab5aa514311c20b83b32cc9.
def localCycle00196 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint c1807434527fb5780df61aea12456c6436c7a69faa72b565fc50b5b9969cd0ef.
def localCycle00197 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint c340cd9efbae87c76be07235549fa6d219747a0c9ccef26b709b20337caee1b8.
def localCycle00198 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint c3a1908c65c33b82540ea3ef708bf5b4d0cebfdf83ad2e0c71397b725328162a.
def localCycle00199 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -2, 0, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint c43051ed279d24c59ac17cdfc437b49462b2ef68636f35d70a56263ef442b703.
def localCycle00200 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 2, .gapUpper 2 4]

-- Cycle fingerprint c45e37aacc1f3ae4c6c3546b595a69d3469bb05fea2822909bda17d34641d03b.
def localCycle00201 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, 0, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint c6a2b96d5ec4c7a0f648c4373f5ca402b9216dc40b12d687f6f72f8bc2e82995.
def localCycle00202 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint c70bb264d0cb21e9a8be3c9dcd2c31c88155a3beeddad631c5177684befa0789.
def localCycle00203 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint c7c8a9f90d5e9478ecc23489e6048c35bd869425d3aa06d637fd8c2e1a547db2.
def localCycle00204 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint c87be0a65f28cc6af32fee5dba91d9c9c7b120b3a58ecdff1e4b0c261feed675.
def localCycle00205 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint c891c0f88dfadb39f9594bf171725198a3e3aed90ecc2fa347e25990c63c3742.
def localCycle00206 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .triangle 23 0, .gapLower 1 2]

-- Cycle fingerprint c979e848d55dd83925d29c3e0630509ac7a732469f22e0cfdf41712442bc36e2.
def localCycle00207 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 22 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint c9b4ee8eaf5e80ffa55ff3eb37118cec8a93e00c6e57c2edc52ce86e3c86ae49.
def localCycle00208 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint cba4ab551c122f96ee96dc2138f5551bb3a6dbc8ca9b0173cbc18343703f620f.
def localCycle00209 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint cbf01ad1e2045a75bd715ed7b46207c690ec342ba18b3167a5bd7716b18feabc.
def localCycle00210 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 20 2, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint cc27dee3670b6513d9f85a3a6e85e0207187be02b9188215220a14624e251df7.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 22 1, .triangle 2 0, .gapLower 1 0]

-- Cycle fingerprint cce24149288d1815d121a7c5c3ebfed482713bfba44c7c5f790bc09e9d051d7f.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d17ffc51a8d0a7757185d9db4e38251ec7b123e06efce7b29667526b9a42c7a0.
def localCycle00213 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 3, .triangle 1 2, .triangle 5 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d38bb8cce2360b284d039354af6bb9c963ea9a699ab0b62d5ac80f8f85a0bbfc.
def localCycle00214 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3]
    constant := ![-1, 3, 0, 0, -3, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 27 0]

-- Cycle fingerprint d4c0a3c8c5b8cab6cc70c23e920a4b8dda08c99e47c923d288e9f692bff2f614.
def localCycle00215 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d52787f98884d170165e139387c5c9dcbd5d941bef8273363acc222a95ba3df9.
def localCycle00216 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 0, -1, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true] }
  origin := ![.triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 33 0, .triangle 30 2, .gapUpper 2 4]

-- Cycle fingerprint d59587a12402bbf0b7428bb757bc33d5383403d314e6ada6ea23a2c8c856f4ac.
def localCycle00217 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d5f00866ad133ab60cec4ec00c784ee67138d1284276602c7c774ff92da861fd.
def localCycle00218 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d943e0c83d37ddd7ddae8507d5a58822843a5c785265b1c66e566d8a00fbae5c.
def localCycle00219 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint d9a8dcc2bd704e77ca33335ccdf6fa215a0dbdb31b321fb7ddbc3acff7dec246.
def localCycle00220 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 3 6]
    constant := ![-1, -1, 3, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint d9d9fee9b823bf16a71f70c16080017de595e75fc65cd9aedd5ab2f5fd4dcd2b.
def localCycle00221 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 2 0]

-- Cycle fingerprint da2aa53f11dc72208dad388ee037c0a345e0721d729e6d9c6f5a895ad4438367.
def localCycle00222 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 3, 0, 0, -3, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 3 2, .triangle 10 1, .triangle 26 0]

-- Cycle fingerprint da834619033a63100255fa38b2fcfc40940cedb932ebdd223aaf3e23fdac5a4e.
def localCycle00223 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 5]
    constant := ![0, -1, -1, 3, -3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 31 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 33 1]

-- Cycle fingerprint db1aa4b06f375c40d5a690b1e786c3fb6035c60d440d6b930ca189ba46682b8e.
def localCycle00224 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 19 2, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint dba072c17f6e8feea179d16729dca0b787a6de3190d547e62d309deb17e03bef.
def localCycle00225 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint dd3d9410651c63036dba581efedd657fb67406610e44b8ad2ec8fa6d4bb862d1.
def localCycle00226 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint dd46cced14f62ca3d64a68a4d414f1079033467db12eb90c76835480cbeaa12b.
def localCycle00227 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint e2527422a23e962d5931d52e46c3dfda4697462b06b2a91f7771cc957ffe0899.
def localCycle00228 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint e2e6e6f61fd9ac7b08fd615e181ed0d9a6c061cebca1702b9a546ded28696a08.
def localCycle00229 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint e2e7000ecc0af58d15c6ad2a7bd77eb25f765ce418497f07ce1fef91057cedaa.
def localCycle00230 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint e50ec3f5beb3beecc761501ca26908c3a2b5319f8945de54b12b064041ae4c7a.
def localCycle00231 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e5da585250f6b156c95f886ed95607637908b310b364f38166466c66356a32e6.
def localCycle00232 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint e82bcd8068f3b03304023070d2a4e304561ebb6c40ffae5319121d6f15e8fa33.
def localCycle00233 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Cycle fingerprint e921f11926b2e8ca376a18b4145f4166db2cdb84822159b07db7da010ce8ecbf.
def localCycle00234 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 2]

-- Cycle fingerprint ea3fcb5fa5f18c206003a808d22f7501eb79749f3dcd84372787faa97ec3f0e5.
def localCycle00235 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, -1, 0, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint ebd5648100c150d3e5e8bca94378a321ac24c566fbeb5bbb04967281a1ae15de.
def localCycle00236 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0]

-- Cycle fingerprint ebeb61c158244ec90326062e1dffcef54d5aa140f33fe5133b104b2702a04979.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint ee7792a0e063614ca1028f3f0a67fb9c4faf48a104445a9d4f10d21adb18400f.
def localCycle00238 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 24 1, .triangle 22 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint ee860112a0de8f5eb1a437846cf795c9722175e3dd9f82373be63c3d824c1e05.
def localCycle00239 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 2, .triangle 5 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ef3b52c5e73c788641f406617334523992ffc63afb45056f9ce80c48f7c4f814.
def localCycle00240 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint f04f61890bf2990d89e72b5117b836de9a9ecc7065fa2f69e2314e5902195936.
def localCycle00241 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint f076f0f5bfc2bea43eaf8862a093a63f559ec4c218e7a47a47193d134a3fddd8.
def localCycle00242 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 0 5, .distance 2 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -3, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 3 2, .triangle 7 1, .triangle 30 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint f157b4271672435a4dcd8c78010ca9d8b6c210677f46f26b26d6374ca6d73b3b.
def localCycle00243 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint f1e8fc5f561ed45fc278eded820c6ff181f3bcc9d8df86bfef1f1d18cb2b06c6.
def localCycle00244 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint f291a2a5e4eae4435df47fc7c4a658ac59efbe41fa29401523ad21228222adb0.
def localCycle00245 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint f2eebc7d7dbeb04391faf06e9c424809a05cf37751c24e1b750f61760dee0e5a.
def localCycle00246 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint f3d754efeb86ce7d44fb0d17225043def156150b190329dd6bdbc007c35f74a4.
def localCycle00247 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint f6c344930ef64025f0ee936ce8a1c60a19f67f5aa8c9ef3573ff4c6f40e58ebe.
def localCycle00248 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -3, 0, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint f8eee56ec2303d898fbc1138cc8aeb18711d9ec48e305d5220faf66d7d7327cc.
def localCycle00249 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint f916cc537e4bca96fac2ab6c97a7fad1bdb2d3abeef208ecded2ac621ecb7b35.
def localCycle00250 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint f93f6ed45ce6836bb47952ac863f55676f612460a6263e6e680a96065fa3fa4c.
def localCycle00251 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint fd039e497f6d4111f4bf79860b182448d3820595d6b84a366037bae1fb74a16f.
def localCycle00252 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -2, 0, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint fd0c1c61028ac450417e3ad1239c4e94b34980e8d8f6d7df2ffa5dad2b6649c1.
def localCycle00253 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 1, .triangle 2 0, .gapLower 1 0]

-- Cycle fingerprint fd61e5446000be16562a60b6aa9f1ed5e904dda7be5a331a8538c5cfa8519b03.
def localCycle00254 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 2, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint ff85703c8be321b983cca5df90146cc45d58f42af4cb9ff779fd2903fb352291.
def localCycle00255 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapLower 1 4, .triangle 20 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint ff8c7ede9096354dc1c695d430be578b0c3565dee8f6a536f5dddae12ad11037.
def localCycle00256 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint ffa7cb39e1ac42b60efa712bc74d06825c860bdb888090bef46f6998aef56d6f.
def localCycle00257 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 4 2]

-- Cycle fingerprint fff6967affd57c3b912ae87e45267565c477a20b9a3577a67a68af7ecfc3355a.
def localCycle00258 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

def library : Library := fun id => if id < 129 then (if id < 64 then (if id < 32 then (if id < 16 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))))) else (if id < 24 then (if id < 20 then (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 28 then (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))))) else (if id < 48 then (if id < 40 then (if id < 36 then (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))) else (if id < 38 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)))) else (if id < 44 then (if id < 42 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))) else (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))))) else (if id < 56 then (if id < 52 then (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 60 then (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))))))) else (if id < 96 then (if id < 80 then (if id < 72 then (if id < 68 then (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)))) else (if id < 76 then (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none))) else (if id < 78 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))))) else (if id < 88 then (if id < 84 then (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)))) else (if id < 92 then (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))) else (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)))))) else (if id < 112 then (if id < 104 then (if id < 100 then (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))) else (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)))) else (if id < 108 then (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))))) else (if id < 120 then (if id < 116 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)))) else (if id < 124 then (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))) else (if id < 126 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))))))))) else (if id < 194 then (if id < 161 then (if id < 145 then (if id < 137 then (if id < 133 then (if id < 131 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))) else (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))) else (if id < 141 then (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))) else (if id < 143 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none))))) else (if id < 153 then (if id < 149 then (if id < 147 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))) else (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))) else (if id < 157 then (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))) else (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)))))) else (if id < 177 then (if id < 169 then (if id < 165 then (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none)))) else (if id < 173 then (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))) else (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))))) else (if id < 185 then (if id < 181 then (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none))) else (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)))) else (if id < 189 then (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))) else (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)))))))) else (if id < 226 then (if id < 210 then (if id < 202 then (if id < 198 then (if id < 196 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none))) else (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)))) else (if id < 206 then (if id < 204 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none))) else (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none))))) else (if id < 218 then (if id < 214 then (if id < 212 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none)) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none))) else (if id < 216 then (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none)))) else (if id < 222 then (if id < 220 then (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none)) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none))) else (if id < 224 then (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)))))) else (if id < 242 then (if id < 234 then (if id < 230 then (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none))) else (if id < 232 then (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none)) else (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none)))) else (if id < 238 then (if id < 236 then (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none)) else (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none))) else (if id < 240 then (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none)) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none))))) else (if id < 250 then (if id < 246 then (if id < 244 then (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none)) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none))) else (if id < 248 then (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id = 249 then some localCycle00249 else none)))) else (if id < 254 then (if id < 252 then (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id = 251 then some localCycle00251 else none)) else (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id = 253 then some localCycle00253 else none))) else (if id < 256 then (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none)) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id = 258 then some localCycle00258 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 4], ![2, 0, 3, 1, 5, 4]], proof := .tail 63 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6528)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 5, 1, 6], ![2, 3, 0, 4, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 205 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6529)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 5, 0, 1, 6], ![2, 3, 4, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 49 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6530)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![2, 5, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 8 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6531)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![5, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 22 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6532)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 1, 6, 5], ![2, 3, 0, 6, 1, 4], ![2, 0, 3, 5, 1, 4]], proof := .tail 254 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6533)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 5, 6, 1], ![2, 3, 0, 4, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 196 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6534)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 5, 0, 6, 1], ![2, 3, 4, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 59 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6535)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![2, 5, 3, 0, 6, 1], ![2, 4, 3, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 69 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6536)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![5, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 54 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6537)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 4], ![2, 0, 3, 5, 4, 1]], proof := .tail 10 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6538)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 5, 6, 1], ![2, 3, 0, 4, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 171 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6539)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 6, 5, 1], ![2, 3, 0, 6, 4, 1], ![2, 0, 3, 5, 4, 1]], proof := .tail 76 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6540)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 5, 0, 6, 1], ![2, 3, 4, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 58 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6541)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![2, 5, 3, 0, 6, 1], ![2, 4, 3, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 33 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6542)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![5, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 176 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6543)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 1, 5, 6], ![2, 3, 0, 1, 4, 6], ![2, 3, 0, 1, 4, 5]], proof := .low (![146, 182, 34, 222, 92, 223, 102, 138, 15, 43, 238, 90, 123, 174, 118, 104, 90, 161, 120, 194, 173, 14, 193, 145, 16, 62, 257, 100]) }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6544)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 4], ![2, 3, 0, 1, 5, 4]], proof := .low (![248, 116, 202, 107, 92, 223, 102, 79, 37, 75, 238, 90, 123, 73, 45, 104, 90, 184, 1, 194, 173, 3, 193, 145, 16, 62, 257, 100]) }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6545)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 1, 6, 5], ![2, 3, 0, 6, 1, 4], ![2, 3, 0, 5, 1, 4]], proof := .tail 57 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6546)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 1, 6, 5], ![2, 3, 6, 0, 1, 4], ![2, 3, 5, 0, 1, 4]], proof := .tail 137 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6547)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 0, 1, 6, 5], ![2, 6, 3, 0, 1, 4], ![2, 5, 3, 0, 1, 4]], proof := .tail 131 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6548)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 0, 1, 6, 5], ![6, 2, 3, 0, 1, 4], ![5, 2, 3, 0, 1, 4]], proof := .low (![172, 109, 139, 214, 126, 11, 102, 65, 2, 78, 211, 195, 123, 191, 89, 225, 195, 165, 252, 27, 153, 7, 220, 47, 210, 162, 4, 186]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6549)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 4], ![2, 3, 0, 5, 4, 1]], proof := .tail 10 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6550)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 6, 1, 5], ![2, 3, 6, 0, 1, 4], ![2, 3, 5, 0, 4, 1]], proof := .tail 10 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6551)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 0, 6, 1, 5], ![2, 6, 3, 0, 1, 4], ![2, 5, 3, 0, 4, 1]], proof := .tail 131 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6552)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 0, 6, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 29 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6553)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 6, 0, 1, 5], ![2, 3, 6, 0, 1, 4], ![2, 3, 5, 4, 0, 1]], proof := .tail 81 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6554)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 0, 1, 5], ![2, 6, 3, 0, 1, 4], ![2, 5, 3, 4, 0, 1]], proof := .tail 131 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6555)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 0, 1, 5], ![2, 6, 3, 0, 1, 4], ![2, 5, 4, 3, 0, 1]], proof := .tail 94 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6556)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 103 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6557)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 245 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6558)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![6, 2, 3, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 127 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6559)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 5, 1, 6], ![2, 3, 0, 4, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 205 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6560)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 5, 6, 1], ![2, 3, 0, 4, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 196 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6561)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 5, 6, 1], ![2, 3, 0, 4, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 171 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6562)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 6, 5, 1], ![2, 3, 0, 6, 4, 1], ![2, 3, 0, 5, 4, 1]], proof := .tail 229 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6563)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 6, 5, 1], ![2, 3, 6, 0, 4, 1], ![2, 3, 5, 0, 4, 1]], proof := .tail 229 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6564)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 0, 6, 5, 1], ![2, 6, 3, 0, 4, 1], ![2, 5, 3, 0, 4, 1]], proof := .tail 233 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6565)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 0, 6, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 2, 3, 0, 4, 1]], proof := .tail 180 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6566)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 6, 0, 5, 1], ![2, 3, 6, 0, 4, 1], ![2, 3, 5, 4, 0, 1]], proof := .tail 18 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6567)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 0, 5, 1], ![2, 6, 3, 0, 4, 1], ![2, 5, 3, 4, 0, 1]], proof := .tail 18 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6568)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 0, 5, 1], ![2, 6, 3, 0, 4, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 56 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6569)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 2, 3, 4, 0, 1]], proof := .tail 18 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6570)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 84 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6571)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![6, 2, 3, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 147 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6572)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 0, 1, 6], ![2, 3, 4, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 181 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6573)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 0, 6, 1], ![2, 3, 4, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 203 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6574)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 0, 6, 1], ![2, 3, 4, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 228 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6575)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 6, 0, 1], ![2, 3, 4, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 66 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6576)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 6, 0, 1], ![2, 3, 4, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 171 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6577)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 6, 0, 1], ![2, 3, 4, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 12 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6578)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 6, 5, 0, 1], ![2, 3, 6, 4, 0, 1], ![2, 3, 5, 4, 0, 1]], proof := .tail 251 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6579)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 5, 0, 1], ![2, 6, 3, 4, 0, 1], ![2, 5, 3, 4, 0, 1]], proof := .tail 216 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6580)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 2, 3, 4, 0, 1]], proof := .tail 209 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6581)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 5, 0, 1], ![2, 6, 3, 4, 0, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 183 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6582)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 114 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6583)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![6, 2, 3, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 74 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6584)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 243 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6585)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 0, 6, 1], ![2, 4, 3, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 31 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6586)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 0, 6, 1], ![2, 4, 3, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 25 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6587)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 6, 0, 1], ![2, 4, 3, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 19 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6588)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 6, 0, 1], ![2, 4, 3, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 25 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6589)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 6, 0, 1], ![2, 4, 3, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 87 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6590)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![2, 5, 6, 3, 0, 1], ![2, 4, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 68 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6591)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![2, 5, 6, 3, 0, 1], ![2, 4, 3, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 68 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6592)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![2, 5, 6, 3, 0, 1], ![2, 4, 3, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 68 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6593)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 4, 0, 1], ![2, 5, 6, 3, 0, 1], ![2, 4, 6, 3, 0, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 200 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6594)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 4, 0, 1], ![2, 6, 5, 3, 0, 1], ![2, 6, 4, 3, 0, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 167 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6595)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 5, 4, 0, 1], ![2, 6, 5, 3, 0, 1], ![6, 2, 4, 3, 0, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 237 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6596)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 5, 4, 0, 1], ![6, 2, 5, 3, 0, 1], ![6, 2, 4, 3, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 244 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6597)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .low (![221, 250, 39, 134, 159, 201, 102, 42, 240, 38, 253, 140, 123, 72, 207, 91, 140, 188, 199, 156, 121, 206, 151, 192, 175, 62, 257, 178]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6598)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 54 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6599)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 176 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6600)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 6, 0, 1], ![4, 2, 3, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 53 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6601)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 6, 0, 1], ![4, 2, 3, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 176 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6602)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 6, 0, 1], ![4, 2, 3, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 61 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6603)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 2, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 83 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6604)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 2, 3, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 83 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6605)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 2, 3, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 83 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6606)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 6, 5, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 2, 6, 3, 0, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 204 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6607)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .low (![164, 250, 115, 30, 41, 24, 102, 42, 166, 67, 44, 234, 123, 141, 51, 44, 234, 36, 150, 135, 20, 160, 168, 50, 224, 158, 44, 258]) }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6608)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 101 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6609)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 2, 3, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 219 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6610)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 6, 5, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 2, 6, 3, 0, 1], ![4, 2, 5, 3, 0, 1]], proof := .tail 189 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6611)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 6, 2, 3, 0, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 198 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6612)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 4, 0, 1], ![6, 5, 2, 3, 0, 1], ![6, 4, 2, 3, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 28 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6613)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 5, 0, 1], ![6, 2, 3, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 106 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6614)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 5, 0, 1], ![6, 2, 3, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 95 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6615)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 5, 0, 1], ![6, 2, 3, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 157 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6616)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 5, 4, 0, 1], ![6, 2, 5, 3, 0, 1], ![6, 2, 4, 3, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 13 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6617)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 6, 2, 3, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 212 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6618)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 4, 0, 1], ![6, 5, 2, 3, 0, 1], ![6, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 143 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6619)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 0, 1, 6], ![5, 2, 3, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 208 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6620)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 0, 6, 1], ![5, 2, 3, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 124 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6621)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 0, 6, 1], ![5, 2, 3, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 17 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6622)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 0, 6, 1], ![5, 2, 3, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 32 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6623)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 71 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6624)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 136 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6625)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 6, 0, 1], ![4, 3, 2, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 226 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6626)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 3, 2, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 231 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6627)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 2, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .tail 60 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6628)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 113 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6629)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 6, 0, 1], ![4, 3, 2, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 113 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6630)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 3, 2, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 231 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6631)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 2, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 60 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6632)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 6, 0, 1], ![4, 3, 2, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 170 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6633)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 3, 2, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 231 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6634)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 2, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 60 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6635)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .tail 256 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6636)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 256 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6637)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 256 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6638)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![5, 6, 2, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 119 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6639)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 133 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6640)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 4, 0, 1], ![6, 5, 2, 3, 0, 1], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 6 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6641)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 5, 6], ![2, 0, 1, 3, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .low (![128, 182, 125, 93, 96, 9, 102, 138, 227, 232, 112, 40, 123, 218, 190, 246, 82, 152, 86, 70, 70, 70, 142, 213, 149, 185, 187, 117]) }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6642)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 6, 5], ![2, 0, 1, 3, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 239 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6643)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![2, 0, 1, 6, 3, 4], ![2, 0, 1, 5, 3, 4]], proof := .low (![98, 235, 144, 169, 88, 9, 102, 55, 148, 249, 35, 110, 123, 130, 77, 48, 82, 122, 85, 255, 241, 241, 52, 213, 177, 185, 187, 117]) }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6644)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 6, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 1, 3, 4]], proof := .tail 217 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6645)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 3, 6, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 1, 3, 4]], proof := .tail 111 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6646)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 3, 6, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low (![236, 109, 144, 105, 99, 242, 102, 65, 154, 163, 80, 179, 123, 241, 23, 46, 230, 108, 97, 241, 241, 241, 155, 132, 0, 64, 5, 26]) }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6647)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 6, 3, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 3, 1, 4]], proof := .tail 247 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6648)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 3, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 3, 1, 4]], proof := .tail 129 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6649)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 3, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 215 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6650)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 4, 3, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 3, 4, 1]], proof := .tail 197 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6651)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 3, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 3, 4, 1]], proof := .tail 197 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6652)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 3, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 197 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6653)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 3, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 0, 1, 5], ![3, 2, 0, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 0, 1, 4]], proof := .tail 21 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6654)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 0, 1, 5], ![3, 2, 0, 6, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 0, 4, 1]], proof := .tail 197 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6655)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (6528 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 6528 ≤ id.val) (hhigh : id.val < 6656) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 6528)) = true := by
  let j : Fin 128 := ⟨id.val - 6528, by omega⟩
  have hsum : 6528 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (6528 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard051
