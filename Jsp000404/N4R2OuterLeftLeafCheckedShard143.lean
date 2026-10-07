import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard143
open N4R2OuterLeftReplay

-- Cycle fingerprint 001074398104bcda7143768c1d0962f7759df38201bc26d998912c99919ec4a8.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 00e666a5e69f622196e95aa90779757ad6663aa66f300857af2be1f855322693.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![-2, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2]

-- Cycle fingerprint 00ef01a5eebf2ffbc8e3c4e39cb5c135a4cf8aec361a5bde68b19c507bcf88ec.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 22 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 0344e0d5eb84d47680109963ff4b3d9e975ebdf363e402821ab517fdbea377de.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 4, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1]

-- Cycle fingerprint 037e765021568e6182d3b6da56de022d37071a1ed4a4b42c45a323b565a78832.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint 075ede76165ff6f908907aa780fe2478c0f3bf6664122d791f5787b4fff16eb3.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 07a978c3c9c6183724e92af296a2ea282f69eb273b55865f202306c04c1e2a54.
def localCycle00006 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 2]

-- Cycle fingerprint 0c957512e9cbcd2936da361f8da17732b7f41fa0b753dfa4ebe0ab8d728a0d53.
def localCycle00007 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .triangle 20 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 0c9d39fb3412a75b20a4bb237984a6dffa61edf290f8ae2ee3a5d80e8509d94f.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4]
    constant := ![0, 0, -1, 3, 0, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 22 0]

-- Cycle fingerprint 0e062679dd53fc032e3f6e777cb75f3946f09e5116253d5467d5c2a8e503a9df.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 5]
    constant := ![0, -1, 0, -1, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 33 1]

-- Cycle fingerprint 0f3478d4e4b2fa91a35970ae3c57d2b7682bf8e10170bf0e218327724b78b2e6.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 0f714e32d37a545598f275b6953c6f34f24fe68ca57be5a176b1973298ca5487.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 6, .distance 1 6]
    constant := ![0, -2, 0, -2, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 12125d0ad65d63552219c55aefc985080a7e072a0d6a095a0686e1f3bc8a1906.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 3 0]

-- Cycle fingerprint 131a2eecea4d3aeaa44a28afad710f8f766df4a2d2eee274d3e32397f5febd75.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 24 1, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 13cfc6c1ef424113de01fe3ff46d62830c7d355135bb0e8a33f566d58001e819.
def localCycle00014 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 6]

-- Cycle fingerprint 14f1faebb55773d87dc8efe966578e0d1e64b6cff6934323b75d6e2a937322af.
def localCycle00015 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 5 1, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 1506f186f00a6fc1a28c1ea785b01689ed63f9879b5bb192fa0cda302eb1bdaa.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 21 2, .gapLower 1 4, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 160ee7669586d79ab2001f21ebfdc6749e1234716ba10823d133f3f05a3d8ce8.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 21 2]

-- Cycle fingerprint 179a23178912cf1459ee19d36a1b2aea640ec110c0ca68f480372d6b5b24861e.
def localCycle00018 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint 17a57987a74236a82f4bc12bfe837489be4b2b1751d5bd11eb94b87b17e00c6b.
def localCycle00019 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 182fefa0aa6b2acd24feb5008e1d75924190ed0458241704193d37edf13f87d0.
def localCycle00020 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 3, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 2, .gapLower 1 2, .gapUpper 3 1]

-- Cycle fingerprint 195be1b48aa6290b889b664d65a2459be4f142f6536b3f7ef7e12d0a8923af58.
def localCycle00021 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 5, .corridorUpper 0 1]

-- Cycle fingerprint 1990c542faac4dbf1f8eca834d64053aa62a20cf53122dfdb776b99ec1d3cc25.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .distance 2 4]
    constant := ![-1, -1, -1, 0, -2, 3, -2, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 28 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 2 4]

-- Cycle fingerprint 1a8b06e199727d7f5393eac76dbc244f6e52471bf18c8c6edca6fe9e131036c5.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 20 2]

-- Cycle fingerprint 1a9ae509b4e17b6933bacbdede2193bbc136ff60902f6e1038882c1d9e04197b.
def localCycle00024 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![-3, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .triangle 20 1, .triangle 15 1]

-- Cycle fingerprint 1aa37bae90f392521d53fef0451d926de3891402edc40ec400ed92320210e9a7.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 10 0, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 1ab9a4fbedb730d2b23f200565c2792a589e05d8094660592b587660b8d19386.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3]
    constant := ![0, -1, -1, 0, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 2, .gapLower 1 3, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3]

-- Cycle fingerprint 1adcb5aa07e4f6ef355a0b285a055b0ad1898140b6f5087115b1dc8b01cb3474.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6]
    constant := ![2, 0, 0, 0, -3, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.gapUpper 6 0, .triangle 24 1, .triangle 20 1, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 1b4315f4a9f6d6f352fca5fa0cdb1e1462af6701c7d2249cd744a9226bb96d95.
def localCycle00028 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint 1d0852a5ec39b9f3fb2d74ef0a7f04b2ed1272dc884efdd7a092c8bf3d190618.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 24 1, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6]

-- Cycle fingerprint 1d2ed6650f91a910af27a93e832e9213412b11a9fc44997146b53cf3823f8dfb.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 19 2, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 1d5d82f084293ae52c6c797afba682e5865286080a829abf24f973d8be065782.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .gapLower 4 1, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 1d6463940fc7150a70a7ce7b6256420143efa1147d65e0d71ac1b81507216ce5.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![-2, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2]

-- Cycle fingerprint 1dd1c034b64505027fb1e643e591eb8c14631c3312e54abe70ac473c76fcc64f.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Cycle fingerprint 1e1346abb1885d546c15a3dc09c6d239e534153e903c25da765df870298a805d.
def localCycle00034 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![-2, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 20 1, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 20122aeff1503fb5ac03ac5d44a7e2396fbf0d9af6f1fe2bd59c78421a066aef.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2087218ff811b62bf0a1b997503ea153bc7155a81ea56c0022a2ab2f0578fae1.
def localCycle00036 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 1, .gapLower 1 2, .gapUpper 3 1]

-- Cycle fingerprint 20d66bc6d426956262a9e39ad7e8850c6835055abe690d33baf07923604b2cd7.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 11 0, .triangle 21 2, .gapLower 1 4, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 22b230a001925f5e20ddc58415b47c0a1a8492cb6ae9d25c0413abc6dca14092.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 2, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 2504a46b975a1a9ed41ba749d4d98714f9de26e78bb1dc068d9ecbff629b1014.
def localCycle00039 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 20 1, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 2526a229cf707470781d74d48e39d0da716fd5c5c1629759077cf3faf07fc412.
def localCycle00040 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 5]

-- Cycle fingerprint 26c3429604b71784b3177181ac8f2336aa9e4d4bb1a0be0e192617545ccaae53.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .gapLower 4 2, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 26e7cb3314cd0aeb2fba7e83a778cb32c1ef717670df14f3127ef105449db38a.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 27157b649ea586af94b38f82a673e7e8c633f1ee1ae658331eb3cf8d69995142.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 20 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 2823da655d22a6dfd5d039282053a53dcf352ac0186ae9373f9df82dfd63cfd8.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 1 3, .triangle 17 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 293d27e74f3a59fe07b2c0de5bad59ddfe8082f3810eeb3d0277a20667630af5.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![-1, -1, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 9 0, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 1 2]

-- Cycle fingerprint 2ad4a40d2edee62fbf43f70a43f6733c892c52c66f752b627b57c8d42e7f18df.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4]
    constant := ![-1, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0]

-- Cycle fingerprint 2bc225856029f80a3992fb7db7c7e97a4d39925f3f26b877659cfc0f272e3103.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -3, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 11 0, .triangle 21 2, .gapLower 1 4, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2ca2c31d8562818ef12586ea7c4d679188dd458e9484b6272de95a59beb0b438.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![0, -2, 0, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2]

-- Cycle fingerprint 2f79fd69b1601a4e7f88c789e8cacb01df1e2d6556e41d19b7f564d9fbbc74ac.
def localCycle00049 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 3098cea195584a4f9e483e10fe3bd4e2edd28018e89c7af0f7b030440a8a9539.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, 0, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 31834a283814f05cf008d79fb7a3c0094ad09adb28be5cac8b1f4c480737ec82.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 31e1ae37d56212b13f2c19525c80b2ff1d0d4fb3d7c0b5ea015b0a93ce5fc4a9.
def localCycle00052 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![0, 0, 2, 0, -2, -1]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .corridorLower 1 3]

-- Cycle fingerprint 320eef3dc59b9dc9ee1432af88d50c80a086a9f172970fb7109c61baef2169b0.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 10 0, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 3232ffab6b4d58d53bc9566dc7e008245edc758ab6f2a2e004f609a1f427df79.
def localCycle00054 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 3495c40b79516f2a5492ff03a178c51e096d4a6c5abce2126c3776c82e49de4a.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3]
    constant := ![-3, -1, 3, 0, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 19 0]

-- Cycle fingerprint 3600fbde3158584c6067c07ab1376dbfe2829ac2fa040d9f0a4325e1d7918ce7.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 364359bdca56063752587979ae8e8b66baa5f98995b802c3932514482da7a9ab.
def localCycle00057 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 37326207feccdfbd335c5e6b2b8f326ccf0d0f577860d33e22778d0e46c658f4.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 20 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 3a46b974bda3bb97e251eafc6a82e15ecb8356b068809f3c02d6d6fe04783604.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4]
    constant := ![-2, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 19 2]

-- Cycle fingerprint 3a9942779e4ce3c8b336eec6d129479a184e3632835780c792a99c4255d56dcf.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3]
    constant := ![-2, -2, 3, 0, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 19 0]

-- Cycle fingerprint 3bac14a32e6a095a4d7222f50a54986e876e4b612bde7585e45dcb72ddbcee07.
def localCycle00061 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![-1, -1, 0, -1, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2]

-- Cycle fingerprint 3bb162786982eb1cd10ebfce8c8e8b5dd9843806a9db897009bb79a745b9a1e1.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6]
    constant := ![-1, -1, 0, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0]

-- Cycle fingerprint 3c18901d4f5112342afe61e1620eb572eace3472819777c6f38a5105a578d5ec.
def localCycle00063 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 1, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 3c58da5f93e230d2daffb99ad7184e250b741f23e807de950d3cb8b767268ff3.
def localCycle00064 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-3, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1]

-- Cycle fingerprint 3cf896383bfdb6afe859a5579988366b77a074fc016309ce257be9a682b35867.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6]
    constant := ![-1, -1, 0, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0]

-- Cycle fingerprint 40545932fa7aa145e1e42b7fa600c16b40f51c3eb25a2bbddf8361857b0b1fbe.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint 40d07733cdc088d30b38b09978de47ed517eea4589e0648e61ddefa63f0c9a4f.
def localCycle00067 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![-2, 0, -2, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 17 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2]

-- Cycle fingerprint 422748179acc8d62ef2ca8108d53978b005f38ca0585464d494059fa4cad621d.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 4, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5]
    constant := ![-2, -2, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1]

-- Cycle fingerprint 4245434994139a4f665797c4a60af945dd7756c0866e86b17cbd863f84f0b7e1.
def localCycle00069 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 431aff5882e7cce047a8a3f80fb02446d70222c5aaaf18c7b4acbfc3a773ac5b.
def localCycle00070 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 2, -2, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 432d5dfc948814bd4550a0ecd809de2c04fa8ed03bd6aa0d069004cd7e7b2cf0.
def localCycle00071 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 10 0, .triangle 20 2, .triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 43992c82ce42650831db2d3de16051c06f33b4c2efae20736537ebbb82f92f1a.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 24 1, .triangle 20 1, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 43fbb43510007e28f57b45243e6aa83f7ee796d17ff0fcc36b0a99f4a1c8a25f.
def localCycle00073 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 19 2, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 44d3b3309e9c6f6736d2696537e275b8f472bf49a7cea52b374f977f2b57cdac.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 2, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 45c6c228234f4be1f5c673d6477ad9d6a64a1e557043cc3815c8f7e5aedf3f7c.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 22 2, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 464bc47193ac296cf9c2a0e2294ddfd401e8d0cb4c08d0a44988b5a83bd8ba24.
def localCycle00076 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 24 1, .triangle 20 1, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 46d1309cfe7c3446e8586c1bc8c745eb516923d056c17cd3068605d2346b518c.
def localCycle00077 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 4769e39099e69b2c4e7e011997ff4b070eb87745fb813a7158c7f1b991a28870.
def localCycle00078 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 24 1, .gapLower 1 3, .corridorLower 1 3, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 49cda761aabcf8c4c720f642233ae907a9662252fe934fb95b89d7c6b02119bb.
def localCycle00079 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .gapLower 4 2, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 49e0b2ef8401a2804ce90f104119ee07cfd5c84e1322a652a33a1cf8a882f994.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 49e916b794f4f23073ab36cc47f2cbf812ddc0010d22dfd6a37fc4d37cfa47c3.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 4a356922d207f0ad48d021b3a255422bc850c3eb70ce6ceec684adf4061dc714.
def localCycle00082 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5]
    constant := ![0, -1, 0, -1, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 10 0]

-- Cycle fingerprint 4a52af54f85afcb8c4ae2404854bb09c99a852f4a7e1a07c62eeb2329e6a3f0b.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 4bb3e4696f0e253f5624cd4a973699e252e98ae394b2fce9db702536263df618.
def localCycle00084 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 3, -3, -1, -1, 0, 0, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1]

-- Cycle fingerprint 4c2e188d34b11e4d0eb68222d26840592c401e035894350618d89e596e4d19c1.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4dc9e936699efffd9a7beac03d765683066f89411f9f65537527040dfb6d749f.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6]
    constant := ![2, 0, 0, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.gapUpper 6 0, .triangle 24 1, .triangle 20 1, .triangle 19 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 4e496cfdf1aef172bb41aaf5bba7e226da81257f9f7f52a95b41134991bd2a40.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5]
    constant := ![0, -2, -2, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint 4fad6d8c6e3e593c5ee5f70b7f2ca4c5a28048cf50c8611f4defee85eddebd4e.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![0, 0, 0, 2, -2, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, true] }
  origin := ![.thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 5023c94764355688ad1653616fa4c0e52bbb08d94c484ff1aeda507c4bc85c24.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![0, -2, 0, -2, -1, 4, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 21 2]

-- Cycle fingerprint 5038570ce344b15daa1b99a073fde6ca7f85b588c6b61482baf3316814e317d8.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 53a55bf93d2c5f6a532b14f43ac6d1bc7596b91f82ee842495c8484858b0c7d9.
def localCycle00091 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, -3, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 55e9bc2548870c05d7f07d833b23465e02d2a0da97a5d0b9cd8be5815ddcd1d0.
def localCycle00092 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 5660844521424eacd90194af1e7ec538bb141651d6a45a3c9cbfc2e7d2768ed7.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 5705a3fee3ffba19fdedb77af9e9ca63014d9849d52e069e29b6671be81f8e47.
def localCycle00094 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![0, 0, 2, 0, -3, -1]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .corridorLower 1 3]

-- Cycle fingerprint 57e116fb4946ca29596ca8d61682c97d467cb6469828953cdc947a04a5ff70ad.
def localCycle00095 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint 5807115fb4a8423dea78aa1ae9a0c442e54795d100a38d2689b8f57816d581cb.
def localCycle00096 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, -3, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false] }
  origin := ![.triangle 3 0, .triangle 20 1, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 585d835e34d980c2b320ba8d8a4c680f79fa72ec1c3dfc32fd5469f345082f7a.
def localCycle00097 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![-1, 0, -1, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, false] }
  origin := ![.triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 32 0, .triangle 23 0, .gapLower 1 3]

-- Cycle fingerprint 59ed5a5cb7070853788b59a17b10a938ef7be39b3a695fa2c0643e5f4299d5f9.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![0, -3, 0, 0, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2]

-- Cycle fingerprint 5a28d79874061aa88c97bb8cfb69957fd192b0ba3bcd40830a8ac0da13553ac0.
def localCycle00099 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint 5c726f8e7a7675da5d0c703b1b1f65e5f03ef9123d409aa2527e9a98e69799e6.
def localCycle00100 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, 0, -1, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 5c96f37054b7bac940bc67395f93a0343906f24aef0015b313d6ef0038777f6e.
def localCycle00101 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 5d0ad4e364da04d6d2e08f64b98eae078288c0d1233cf7e9eb8068efe7c5fd86.
def localCycle00102 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 5 2, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint 5d9ab4e7f9b571fcf41ddf025c2d1ca80d6ab432c3db835fdc6463a842b4e0d1.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![-1, 0, 0, -1, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.triangle 11 0, .triangle 33 1, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2]

-- Cycle fingerprint 5f68e10cc83a0c2882ee89a3a82467bf42e740e786d472352325c7c886e4af4f.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 1, .triangle 20 1]

-- Cycle fingerprint 5f7e2dd48bba0c9ce311dd97964b0f6d6c419a194c5bc7825738b77d91409739.
def localCycle00105 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .corridorLower 1 3]

-- Cycle fingerprint 61055e61d8a5acc462fdbd1f076f99fd1fb77e0615856393ab33c7309d64a186.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 626e5726b84927bc74d27b8d975495f0c064600fdc5d657d4c3658dc801252f7.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 2, .triangle 12 0, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 627bc692b12051cb442ef9a5affa3ce2e825f868658afbdd0f6a76606d851455.
def localCycle00108 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 636daeab0f21900f625a8e376ad9880aa4bb8682f6e405c85aa28752af749f61.
def localCycle00109 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![0, -1, -1, -1, 0, -1, 3, 0, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint 642a0776d26fad31693c43110174c89348c6c37cfd8bb64f3ec7230921ed09f1.
def localCycle00110 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 65da408403662c84d7ba367384ad9df2e50a6ef92e4bedfd7a8d56dc100eb3c9.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![-2, -2, -1, 4, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 21 2]

-- Cycle fingerprint 65f91e135f70912f4002c6182373c961037e01a00c40448ab09790f50e1d7f70.
def localCycle00112 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 66d02207a0a7279029f7c3291817f813e4c1c7e210501a5a1cdcde3ca4286d5c.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 1 3, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![0, -1, -1, 0, -2, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 2, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint 6848d42af061e291534c1b627d71ef825b3eff8a5633c79d043d7e36e663463d.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 6910fbc9c7d8dfb5ed7ccb174273b4f191a0414779004ec61e108de97d605a22.
def localCycle00115 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, -1, 0, -1, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 2, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 69e6d4bd20a7dc469697f74a9469535f8248e53283ebdd2815606c94bc895035.
def localCycle00116 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-3, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1]

-- Cycle fingerprint 6ab4ef02b9aaf176b37b9d669d5800eda5df05097f2700512c05077a3fac961b.
def localCycle00117 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 6bff74332cd15780b3d1216b99257afb55b321507c637a7ca100b1dac54738b6.
def localCycle00118 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4]
    constant := ![-2, 0, -2, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 18 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 19 2]

-- Cycle fingerprint 6c00eec610f299138187563c3f398ba3f57505c0737014fd55ecd20e0d6413c7.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4]
    constant := ![-1, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0]

-- Cycle fingerprint 6c8c7f88fe3dcd067ca327cdab876bee98912075f84d56e7b5455c345f4edeba.
def localCycle00120 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![-1, -1, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2]

-- Cycle fingerprint 6d20883987f0b04c38a6c58e0cc3312c7a4939b0505e055faf1981da778f3a44.
def localCycle00121 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5]
    constant := ![-1, 0, -1, -1, -1, 0, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2]

-- Cycle fingerprint 6e910df43eae30b9de9387fe8963c37923d6b0eaa25ab44bccdc4706f20c5775.
def localCycle00122 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .triangle 15 1]

-- Cycle fingerprint 6f7c96d2b2799bc325458d31167c9a08293667ba85352101138bd0bc2a71935b.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3]
    constant := ![-2, -2, 3, 0, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 19 0]

-- Cycle fingerprint 7259d913abf72cf39e13ef91f091ddc0e73ba3cfbd4c0a36d2bd31fc9ebc02a4.
def localCycle00124 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 7320949ce6e507f36e93393eceeec244d26a39ecf01577789dcdca13150c157b.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 2, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 73f3f6dcd818f2d513b755968b14e5f68331dc986cd7ecf0555019e7094a91ec.
def localCycle00126 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 18 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 74e6635415fda9f38dabe0dcb10a9ed4ee7b8f8438f5cb0b5f0c9223583e0226.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 75e4631cdd36576d47845123a61ddfa54b95fda22f798fd232dcad844d4d8723.
def localCycle00128 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 760861eea4dff5ca2cfd638931edebddedc3359ac70773ed1bacfda451592c4e.
def localCycle00129 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![-1, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 9 0, .triangle 19 2, .gapLower 1 4, .corridorLower 1 6, .gapLower 1 6, .triangle 1 2]

-- Cycle fingerprint 765831254d3d3bd8767df74fe2776b356c15436e9f3ad7dc10a9d0cca2f7ec8d.
def localCycle00130 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint 7673df9bb9f4df5d81082eeac6877919d7bf4b724735d57178305e261cbb4301.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 9 0, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 7697d00df10771d18dbb170450fd2e37ec690ea27a3ca8f3c1fb7f5161382b8d.
def localCycle00132 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4]
    constant := ![-1, 0, -1, 3, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2]

-- Cycle fingerprint 77236d6af1163e1ea58535534ce07fdfffee09cfbbbe836934b4f508a6e1fcbc.
def localCycle00133 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint 7887243c8a21946e8b3ec6716de781f3ef72f56e8a57de0c2b037156528be9bc.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 7a599a3c8311138c10d39ace607bfd4f1c70996723136750febcec32882724cb.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint 7a94a3ed6e780c8feb512dda168694b14fcd397e1b21e1b26a3e5188fe3ef135.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6]
    constant := ![0, 0, -1, 0, -3, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 33 1, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0]

-- Cycle fingerprint 808d77a7fe3a5dd99902da593055bacfe19c7e0fa09605056734deb96fbde055.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 80a7976cd090a254d5fd9642082c58933985bad57c6263f057b3fab02fcef0a7.
def localCycle00138 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![0, 0, 2, -3, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .corridorLower 1 5]

-- Cycle fingerprint 80c3b536d9465845ada24b47fed894810be479a6d73a97134bf06bcf7a193e05.
def localCycle00139 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 1 3]
    constant := ![0, -1, 3, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 34 1, .triangle 31 0, .triangle 19 0]

-- Cycle fingerprint 81427d2c78f03357e25cb8b2c043c7a1e3b435cde1d8656cc1b5fb9f6de8aae7.
def localCycle00140 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 4]

-- Cycle fingerprint 8169b727e266f442ac804b920b0e2e016d8257d81afa7ad8f30f05cdd58d591b.
def localCycle00141 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 83d797e17acaab777f6b7ca7348e66202ea56cdf3c7c3b99fb2704025066c2da.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 5]
    constant := ![0, -1, -2, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 33 1]

-- Cycle fingerprint 84baaaacb29a55586f2338c9fdc8a2c430b16730c1b9b2b42dfc52d27dd262f8.
def localCycle00143 : Cycle where
  length := 6
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 4]
    constant := ![-1, -2, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 9 0]

-- Cycle fingerprint 8636272df030c2bc731e18854f0d3077fe5e20a0d63fefc4b1b90268916f0c69.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 8687544900248b00d6266c4ca869a89301c4f4038b0af83ef2a030d00a398c75.
def localCycle00145 : Cycle where
  length := 6
  data := {
    node := ![.distance 3 4, .theta 3, .zero, .theta 5, .distance 1 5, .distance 1 3, .distance 3 4]
    constant := ![-1, 0, 0, 2, -3, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .gapUpper 5 0, .gapLower 1 3, .triangle 19 0]

-- Cycle fingerprint 87278e1c8508982e4ac322482582e8410910d7af50cbefaa1a4b2063c3cef7a5.
def localCycle00146 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 0, .triangle 20 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 8880090a011db507eaa7f4b1fbcfe3f90d63838000df9de17736a75c88400865.
def localCycle00147 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 4, .corridorLower 1 5]

-- Cycle fingerprint 8914a67b6eada5b1cd82d7294bd0351de515bcb7b844849896a118a1330d14d8.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5]
    constant := ![-2, 0, -2, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1]

-- Cycle fingerprint 8c8e5388a06731117cfa99a96dc0e57e879e12f763ffa26c8d9519264d1693a1.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 9 0, .triangle 19 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 8eb3308bac621c5906ddce7182201b8e61c8f9fba80a326c66097c2f407aa70d.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .triangle 20 1, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 8ec9f52007474fa82768b14fe010f3d1cc8bb24b1d672773fdbbde2dfdbd8fd8.
def localCycle00151 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![-1, -1, 0, -2, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 1 2]

-- Cycle fingerprint 8eca7849f3f5d1fa6beced77753b7d1d776ad17e5b3ff066cab5ac66ab0e8941.
def localCycle00152 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint 90db499cc4460abbfa04aae413bfd81923a3e54c82559cd451596be68fc91f7d.
def localCycle00153 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 5, .distance 3 4]
    constant := ![-1, -2, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true] }
  origin := ![.triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 33 1, .triangle 31 1]

-- Cycle fingerprint 90ed888ccd250b539b66a663bdedb717d535fb7505cbb62ebb9984e01afe255a.
def localCycle00154 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 912f1843c455f41bd3a2b2cbdbdf046ed6c30da177e0c282cfffa87b0722890a.
def localCycle00155 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-3, 0, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 20 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 919a7cef09b044788840a24539a66ff776205a4f4ed063854c6fca47582196c4.
def localCycle00156 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 4, .triangle 15 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 91c80a1bc661fb70625f6fdef6e47a37b77af3ea224cf2cdf62d35ffd3fcaf27.
def localCycle00157 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 32 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 954a2c7303cfa38e7a8338556ce77431ca7939ffd142699ad03c512feb2c000c.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 5, .distance 3 4]
    constant := ![-1, 0, -2, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true] }
  origin := ![.triangle 19 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 33 1, .triangle 31 1]

-- Cycle fingerprint 960ac0c52a5b4808fd2f55a508772f74bfbc7bf0cb58e5d99436ae5eac3cd9ed.
def localCycle00159 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 19 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 96e58ccf38ee68974f674384b74670c14e4a4eedd12f0ff333b397744a290189.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint 970dc2b6ad55727b231c1856b71f34619e2f5f982c6ed88a8483b4077bef04ec.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6]
    constant := ![0, -2, 0, -2, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 19 2, .triangle 23 2]

-- Cycle fingerprint 9722f53f1f9a05edc75177de46af5464ff2ae801fd78b474a39779611a51fa7c.
def localCycle00162 : Cycle where
  length := 6
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 4]
    constant := ![-1, 0, -2, 3, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 9 0]

-- Cycle fingerprint 9845e2c17178490a68aa8ae4603a575bd2a80d4f78c13cac1b6191b80cb8d79a.
def localCycle00163 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 98fac646fbe8f655f2d2fbc9ae605f5c79ed7c7409684fc379a19cf3cda449fd.
def localCycle00164 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .distance 2 4]
    constant := ![-1, -1, -1, 0, -1, 3, -3, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 28 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 2 4]

-- Cycle fingerprint 993566884aa9c7c7fb0aa6ecb02bbafa2baedc0641867912472b403fadb6b45c.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, -1, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 99c31db1f3bbbe91cc0aed81570b4708b8ff7c53354a44b6586d4ce7a6f96353.
def localCycle00166 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 5]
    constant := ![0, -1, 0, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true] }
  origin := ![.triangle 31 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 33 1]

-- Cycle fingerprint 9a54d1be9bb60895503fd9c01f89691fce84cb9fdcfe2f12422de6d6483a41f9.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 3 4]
    constant := ![-1, 0, -1, 0, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 31 1]

-- Cycle fingerprint 9af972128589dc141f83b4ce11524a13edd5de7e49dee1940564b7e819901a79.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 9fa7638a7aa42cc0f849f685f270b70cadecc709ada22d9d668735f75ec5b514.
def localCycle00169 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 6, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![-1, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 10 0, .triangle 20 2, .gapLower 1 4, .corridorLower 1 6, .gapLower 1 6, .triangle 1 2]

-- Cycle fingerprint 9fe323ca1883962b51c32988bb1d5b97938103d2ca2e302422e1526f25b28f1b.
def localCycle00170 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 2]

-- Cycle fingerprint a2601035bd31534f712076e0fa64b3538d32bf8ecf36befeb4c15c5b7709a115.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 1, .triangle 22 0]

-- Cycle fingerprint a2e21a23bf79e716c6a666e5ab5be4c99654fbff3947c382d1fa2fe80353f963.
def localCycle00172 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3]
    constant := ![-3, -1, 3, 0, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 19 0]

-- Cycle fingerprint a443acdff3e0361b9495e681bc1d8f5793db1831bdf21593e577233c997592f0.
def localCycle00173 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 24 1, .triangle 20 1, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint a4a0170acc9e8f13646472e5ed1296ced5d1de313ec9bd6c2f367999953290e4.
def localCycle00174 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint a77c240576b4a78dfdd0187f9138d2deb3494a59e1256284e4a448f208d68343.
def localCycle00175 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 20 1, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint a8541b29314b85b31599aa1da3bda24c996a59d82f023fd24df74c85d712d58f.
def localCycle00176 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 9 0, .triangle 19 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint a9bf58b6e1b18dad64861b40fa948309fb4d89eec6a3219df19b0f9baab6b8d0.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 5]
    constant := ![0, -1, 0, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 31 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 33 1]

-- Cycle fingerprint a9f79393ba8b4dfc7493a42ff4c842bb4a6d40e984504148e208d2a77d531564.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 21 2, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint aa8bf3d77484e675057cba8e203ce2e3645201710411d1d02e9ec9c7ad0dea74.
def localCycle00179 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint ab48d12b883711150e543a1e2a36be724318a713df4bd8b1043f00beccd74b49.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6]
    constant := ![0, -2, -2, -1, 4, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 9 0, .triangle 19 2, .triangle 23 2]

-- Cycle fingerprint abeac9dcc615851fa26502687436b58307bbd3aa7e5db43ca01cfc9be4dc9ec6.
def localCycle00181 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3]
    constant := ![-1, -3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 4]

-- Cycle fingerprint ac8aa27a0fceb83ff8ed663077149d05a4fdbd7cbc61aa4a80beb99712e4dc1f.
def localCycle00182 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 21 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint acc8ba164bc9869fe56f530c51d94724ae71a6201f871430d03b421dd5704025.
def localCycle00183 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, 0, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint ace0d4047d90b79ec0964d019140b394e61a7da8b23e5650b2357215ce954489.
def localCycle00184 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint adb9baf9b37bf6b49e3d182cae61c2c86f54869ea1c81b4662bb0b5df558f87b.
def localCycle00185 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 9 0]

-- Cycle fingerprint b026a66b7f20974ebbb2eb986929092d329811e737246d02afa774484b781261.
def localCycle00186 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 19 2, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint b079e757cbc3241adaaa9af7219dd0ff52b51da5198758c793e7b844a06095bb.
def localCycle00187 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint b1a5b1b536b777bd1edb7fcd8e8842df4eded09c258524bd731520b0b952559f.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 9 0, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint b360ff9d7e705a60e1c385526b24e2c1405b08be3fddce25f27e5a01153ec913.
def localCycle00189 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, 0, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint b378251cd7a2ec263799f101d3969494ad3ac569b2bfa029fc88a2e0f1e14aa9.
def localCycle00190 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 20 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint b441ca7df13e878e31b35b392dd337acf4d29e17df2c3ad9083c1dc0592a526e.
def localCycle00191 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint b494585c15fa3b0c9a6e18a300ae83fad2370415d325401b354b5ff4c793c017.
def localCycle00192 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint b593cf8a9788eba087f7b70173c557bb07e4ce6258104ae0a217f62a3c5e7128.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 1, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 4 0, .triangle 24 1, .triangle 20 1]

-- Cycle fingerprint b6b59316150ef2f83c61502c3f4ea14f5644ed787644632f729a0506240339b6.
def localCycle00194 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint b72b0c84894aa0854616665225cd457c6edc67d5cf2e27f8288b56f5858b8a5e.
def localCycle00195 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, -1, 0, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 2, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint b9b6a4bb29c81500c5d3d2ddb58c9fa88360b2318796b4e35f8238b908dbbf1b.
def localCycle00196 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint ba1f4a80f558c4a698d7e586e50f1a0d85062f7363f78d9c6bce3336db2d028d.
def localCycle00197 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 1, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint ba939841515432c85dc3b6ead80330fe14d8f5ca56b4055cb7b62a15266be897.
def localCycle00198 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 2, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint bb2a1bae2c844d1c05a43da727f98421c6bb830575512760d1ff6a71ea5b08e3.
def localCycle00199 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint bb6007472f1eeecbe33f43a7956a1e83f6ab1edc689f9426133cbd1db009733b.
def localCycle00200 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4]
    constant := ![0, -1, 3, 0, 0, -1, -1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 32 0, .triangle 23 0]

-- Cycle fingerprint bc71df181cf3a6c33daa4258193401e53976d75dea42e6a97a1cfd2be78cd9b0.
def localCycle00201 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint bdcf0779573cbb110b4c9a30f0d413a766fc697890c35cfbf0746ee77878b961.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4]
    constant := ![0, -2, 0, -2, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1]

-- Cycle fingerprint bdd0be2b03f9d038a5e51ec78c602b8ee9d147ec3acd092cad78dcb129153637.
def localCycle00203 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -1, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint bf069f86d7d182543d94c206fa5baedb2eba3a91941a84a96a4d6607766b1c15.
def localCycle00204 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint c00388e76c51f92b117d46109bc7a0f260f32b291fc71343e52b826915f0b1b0.
def localCycle00205 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint c102d817aa48ee14ca314a07b5792f495c341003f460ad6e7b37360154ec9206.
def localCycle00206 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![-2, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint c1bfb305ba680283d7e1f18b47de4c57a69f2fe168dd86739e25d62d5a4cd6f6.
def localCycle00207 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 10 0, .triangle 20 2, .triangle 22 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint c2531e03659be2a2a5c7680a3acaf14a74159dc30b246a9b91e9f416cf804ed6.
def localCycle00208 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 33 2, .corridorLower 3 6]

-- Cycle fingerprint c25768ec9d3fac334707fd4adb61a1a905699c6a7afc1a2eb184dae13b949a8e.
def localCycle00209 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 5 6]
    constant := ![-1, 0, 0, 0, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 33 0]

-- Cycle fingerprint c2939c54ed3cc46487b358b4db35b2a8b2a11ab5843299b5add7964010c48378.
def localCycle00210 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5]
    constant := ![-2, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 20 2]

-- Cycle fingerprint c2d54bc0417140f325dec3e854544668ed5826f7d4c5bf96282aee7f90e7c668.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![-1, 0, 0, -1, -3, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.triangle 11 0, .triangle 33 1, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2]

-- Cycle fingerprint c2d90e3ef7eb73744559c0d23580f3095c66f304ca3ffc6fa949ea9317e23447.
def localCycle00212 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint c3a4fc9771aba7c3a674203376f36f491459d097d4e0505dfe707b5207290df1.
def localCycle00213 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .zero, .theta 6, .distance 1 6]
    constant := ![-2, -2, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint c6b8a19b8a19bd4c1dd46271d321fe26b2d3c67e9cdf2d1b62afceea6a2dc0db.
def localCycle00214 : Cycle where
  length := 14
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, -1, 0, -1, 0, 3, 0, 0, -1, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false, true, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint c7662758d44a2586a237a1f1e07b7a0d95ec4ad6660373f39f3016cd74472513.
def localCycle00215 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 20 1, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint c81e3e237c765d1685cde17c0efd5ec7c24559dc6b731801372b2db9ee087455.
def localCycle00216 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 5 1, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint c82196962e58d7c4e8564dc9ba61bf0195644410e98433a770a1ec47fb670a77.
def localCycle00217 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint c85cbf3386575267cb9311b7e235710b74c02a966aa0353b6648bccd7ce2ed7f.
def localCycle00218 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2, .gapLower 1 4, .triangle 22 2, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint c96c62ffe21ef902d0bca3832d206a4e9625dfee4d59390590a33330b0dc36f0.
def localCycle00219 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6]
    constant := ![0, -3, 0, 0, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, true, true, false, false, true, false] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0]

-- Cycle fingerprint ca3f3717c75d4399e5d2c5344d89696254756596288a2e2710a52e2f26c6b1e4.
def localCycle00220 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 2, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint ca403ddc346575cf8f8711bd1cb51b9eacb270140e50d10a4ccb4d21721b9650.
def localCycle00221 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 20 1, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint ca7a719fb297c9187cdfe933821ab783cddc9771408ae639e160a700a7668dce.
def localCycle00222 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .gapLower 4 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint cad7be12b726794ac311a8478121a5c303db40ffa41ad84c985ef21514796f6f.
def localCycle00223 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4]
    constant := ![0, -2, 0, -2, -1, 4, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 9 0, .triangle 19 2]

-- Cycle fingerprint cb143151b8870039fd599ad99d064bdfa9bab38e89434f6764659ed2ec526bc5.
def localCycle00224 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint cb84f473a2b56133e2cbe85a91abd52314551983a2c592bc5670b80d2e3d9e74.
def localCycle00225 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint cbce51c79b47047bfe71ff8a92d5eed91be502427b2fac630b874e8d6f35038c.
def localCycle00226 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![0, -2, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint cbf2a046a34307cee8a33973ff8529586d5b35bfe7d301df2a64527f486d1ef6.
def localCycle00227 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 15 0]

-- Cycle fingerprint cc45ee063445896dc5d691a542608f1e503f3cf81252b12f62697fc0c8f56d97.
def localCycle00228 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 2 5]
    constant := ![-1, -1, 0, 0, -2, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.triangle 30 0, .triangle 33 0, .gapLower 5 1, .triangle 22 1, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 2]

-- Cycle fingerprint cc551e1a4719c839be7fec4e1729f1bb30ecedb89cca207a76aa9e4dfc09910f.
def localCycle00229 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, 0, -1, -1, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint cc99576c139647ffffeb4aee17b9a6a9cd6f5f57b988c31c0dbd3d6ea14a0fff.
def localCycle00230 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint cce21a84ca35213500325bc071de6549d5a14fc6a0fe3d3d82961a83b71b67fb.
def localCycle00231 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -1, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint cd0128be9317a036ef7b7738ac411a58ef4f3aa49973790174e078bde1f41c7b.
def localCycle00232 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint ce19faa6dc5a6132fd57f439170a6199768b2afea48048bc9a52b3c232028e4d.
def localCycle00233 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint d0cf1b7ac603917c6478e64c12d37698f136a3d04c13fb6b9638167f591f7603.
def localCycle00234 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint d1e72269bbb0d85a8f479c32613a3f283e7982fe9c2637db3f21079bf8a285a7.
def localCycle00235 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint d2d7c6822904555104652801474ad8d4fad29176498ce8ffc989f95b81d801b6.
def localCycle00236 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 5]
    constant := ![0, -1, 0, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 33 1]

-- Cycle fingerprint d30c1908c76efc48c0c78c5ac5166630530ef61bce0321a4b28a644bc960e0bd.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint d34479a5e6222402ff2f5b55b319d56597f1b5e94a35deb3489d1925be8c5046.
def localCycle00238 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 2, .gapLower 4 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint d413ecedf532a82fd9766d3c55b825f566327f5f65a030c1c3005161020563ba.
def localCycle00239 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .triangle 20 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d47a286e5cf878139d25cf29fd9a55cf66e1f0336c89c2c0419e47901382d4ef.
def localCycle00240 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, -2, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 24 1, .gapLower 1 3, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint d50d9619c20b7245b6d2aa99a9f50c2de7e5c32f35a68e5ac90eb5169acc3a1e.
def localCycle00241 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, -1, 0, 0, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 22 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint d5a8c8ce5bc43e32ba4665d479ea834738aafe79d09000a278466e4e313234c9.
def localCycle00242 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5]
    constant := ![-1, -1, 0, -1, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 12 0]

-- Cycle fingerprint d72e06ce3734281b379ddbb464df8aec6786d78d2c3b862c5f4dc2acd9304f4b.
def localCycle00243 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d75a4bc2a11cf33928b8ff5246435cc78c4ca9f54575b6fac1052292a6301296.
def localCycle00244 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 19 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint d77278304cb4c36c85d094711c7962a7810b364c7a50b1bea0d2b2795b4ca3a2.
def localCycle00245 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5]
    constant := ![0, -3, 0, 0, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 20 2]

-- Cycle fingerprint d8bd5b9e91e906cfafa118a1043db9eb45b831d0be00e1149d83110e1bbe858d.
def localCycle00246 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4]
    constant := ![0, 0, 3, -1, -1, -1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 22 0]

-- Cycle fingerprint da0282a53585b453b67637c1de39e93fc6875ad525dbe5913946b67bac415863.
def localCycle00247 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint da8bce17f2a93c850929715275ef507b31b27518bf3ecb2146396e00f2282b08.
def localCycle00248 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint dcdd0100c9074ed45dd95c10601672e4613fe1abb46659232734bf961d9703d7.
def localCycle00249 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5]
    constant := ![-2, 0, -2, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 18 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 20 2]

-- Cycle fingerprint ddd45503647eb6a86a5c65665f2b5480d2024eeb1a60693b023280c2c04660bd.
def localCycle00250 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, -1, 0, 0, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 22 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint df9256c10ca1f4848c302650aaeeded18f6001e512f111241fb6f60d048dc565.
def localCycle00251 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e0e424dd6ce91896454185905eec4f1e7b151d98b1ab3126dc14a4e8f1ec030c.
def localCycle00252 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e1959b6b7b21ecfcd74b35465abe35820882c4478f5608b5e5e7125f9d1b3cd0.
def localCycle00253 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 20 1, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint e1d3346e7a6e75de99f1af128dca4ecd88a0e91692eb5c0780a1cec5580b5663.
def localCycle00254 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint e202a305708949c9102deac926d3052410d27e4f1ba4ae798f433da20c231485.
def localCycle00255 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint e20fb73c42b4fe1c46e24ad81ee8df945749ed5485157ed01b784aae6f4072e7.
def localCycle00256 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 9 0, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6]

-- Cycle fingerprint e324c83c287d11c770f07fafd37dfe8f94c58124a8cefba4b0c4ffece73bf1c0.
def localCycle00257 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5]
    constant := ![0, -2, 0, -2, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true, true] }
  origin := ![.triangle 22 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint e4a37e634f243cbfb43cffc4fb930977b5a2b5d3194ce35d94e5f92b5f6327e9.
def localCycle00258 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5]
    constant := ![0, -2, 0, -2, -1, 4, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 20 2]

-- Cycle fingerprint e4faee52696377b129d94052c054401d7001cf8f5988ba6f5cab2df0bc8ca0ee.
def localCycle00259 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint e5e79b8918abf24c20b6987b87d37aa4b479cfb2c8ac1b2ec5f63cb76ad089b2.
def localCycle00260 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, 0, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint e6fd75b192dc119fff462b555338452c779c1ae07411a53eb23ae878b9401901.
def localCycle00261 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5]
    constant := ![-3, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint e7132a3165f904f993b2637ecd35889528ef62e98fed9412c2aeed58f37eed44.
def localCycle00262 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 10 0, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6]

-- Cycle fingerprint e79c4426378e453cc9c84b813d6db0dcd8827e26b7a59258354d3400612e96e7.
def localCycle00263 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![-2, 0, -2, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2]

-- Cycle fingerprint e80ae82ddc938ce8d8bb05c6dc81e63cbf1e1f5910fc81ea889e877ce51cddab.
def localCycle00264 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e83cfddab0ec1be74cf75d48fefdde28a20889286c9ec3d23eb56d9ac7083529.
def localCycle00265 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint e9246b3084c1d3c14373320f9770d14fe0d29364d06e6c035cffaa5d65c712ee.
def localCycle00266 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, -1, 0, 0, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 9 0, .triangle 19 2, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint e966f51eaab4be894f0ed6d7903a4b8fd557fd3bd88fdcd9edfc0a1b9013c6db.
def localCycle00267 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 6, .theta 3, .distance 2 3, .distance 0 3]
    constant := ![-1, -1, -1, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 9 0, .triangle 31 0, .triangle 22 0, .gapLower 1 3, .triangle 21 0, .corridorLower 3 6, .corridorUpper 2 3, .triangle 5 2]

-- Cycle fingerprint e9c4c82f17723fcd2b988eaae284ad854139f4419b9781af286e0b98e8783bdd.
def localCycle00268 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 19 0]

-- Cycle fingerprint eae5aad3c25edbcb1da4cd72a9598050b10841b7214ff97dc74871724a924f36.
def localCycle00269 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![2, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 21 1, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint eaecf89595311e06867164683afb8e7696a6f331de8af42c2376522377208b70.
def localCycle00270 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 4, .distance 4 5]
    constant := ![-1, 0, 0, -1, 3, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 31 0]

-- Cycle fingerprint ebfc22905d345b6eaca3bf2e679cb20d0b8a02b27c13ff269eee2ab1a701ba53.
def localCycle00271 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint eeac4aa8d9dca458c4d6e17bd5117fbaf0199e0ee994315d3a66f8aab84434a6.
def localCycle00272 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint ef8403e70c803d61ca99c4e7f22eb321bef24fabb021b6c03d48edbc9ac5a735.
def localCycle00273 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .corridorLower 1 3]

-- Cycle fingerprint f03de1ac3e65b7aeb44c2ca4caa0a2c638c2b64e544e3ec34020ee123298fc02.
def localCycle00274 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint f05337491600175e0cccdcd88cf3589a3a4806efd1f714ccc2a152b658049b9a.
def localCycle00275 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3]
    constant := ![0, -1, 3, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 31 1, .triangle 19 0]

-- Cycle fingerprint f1ddea0642c75a3605ec0e37a88b9f42ec6ffe53669e176a362f0b3897e41a08.
def localCycle00276 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint f212f464d63b6fd0d5f30e3aa0b892d99cb3c99eed1e899b92d9f5dc0ac3311b.
def localCycle00277 : Cycle where
  length := 6
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -1, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .gapLower 3 6, .triangle 33 0]

-- Cycle fingerprint f2f3c9daddcfb3b6c98cf16eda8ad8203fb76f0f629cf38858ea3bdb6fc7c73c.
def localCycle00278 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint f358bf0f39bf1e5eff30388bfdeb99e09790a313c880357f40cfb623fc93acbc.
def localCycle00279 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint f45368da01f521bb6ab76a793bf796e6f5a2207f0b545e5ed8deaf6669b6c9ef.
def localCycle00280 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![-1, -1, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2]

-- Cycle fingerprint f54294cda17e9708284108a88a026d987d810699474289cf88688ef6559d5766.
def localCycle00281 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 4]
    constant := ![-2, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 19 2]

-- Cycle fingerprint f55dde6233a9bbe4b063e56852ea082281522e9be247f616c047dcbb510d1e3c.
def localCycle00282 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint f73a665268321a758c8f37af687ab982bcac7c71c7eed9ef1a164dd1577230e2.
def localCycle00283 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -2, -1, 0, -1, 0, 3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint f7fd8aae09aba0323797d734a31c105882e915e36536f5f10989983c66451787.
def localCycle00284 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 5, .theta 1]
    constant := ![2, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 1 3, .corridorLower 1 5]

-- Cycle fingerprint f8956432bf5bb39f46ca001fc8d2ac149f57409128b6660f15c7c81325008600.
def localCycle00285 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint f8a2620298965c8c611dd082f559e31e62dee6569477782406381e86b37488e9.
def localCycle00286 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 24 1, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint f90168e7c273ef58555bff56cf0e711d79f884acf0937f89f57c58c192934351.
def localCycle00287 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![0, -2, 0, -2, -1, 4, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 21 2]

-- Cycle fingerprint f920a2cf6cf57d03969a21c78ede39c6b513814334dedc90d140862bfd13dd43.
def localCycle00288 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint f9329d467fbc1437f613a3bab9a9f6f1bc9e37cdc742b713aa28fda99361395c.
def localCycle00289 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3]
    constant := ![0, -1, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 2, .gapLower 1 3, .triangle 19 1, .gapLower 3 0, .corridorUpper 2 3]

-- Cycle fingerprint f96680094a656eaf5a62c043cee72cb2f203b32254ba98f859c28514ec76a7a0.
def localCycle00290 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint fa1cd27c8d6bc98b6a0c34e28637e8b7b337fc38cdf61d1d684ae5878066d3f1.
def localCycle00291 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint fb5e26fc0a9ac4ecc655477ee993168142d23f4ae77eb414a44c9b66fbfc3948.
def localCycle00292 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint fbe5d4608c3bef8363e7ca3234812e167e8fd3f07ab9532b709267dfb82fb077.
def localCycle00293 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint fbe980ea0adf9d28ac640e63a27f510f8090821d6b04df22db6aff4fdbdf47c8.
def localCycle00294 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint fc8f663c3b07cc0a0017913f5f488730f00a7c2007f1acd45e5615a424a4eee6.
def localCycle00295 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6]
    constant := ![-3, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 19 2, .triangle 23 2]

-- Cycle fingerprint fce20ed5f2db30c2bf0f0d5affe8b3c691e0e760910dbe2f276da6f0cd9ca48e.
def localCycle00296 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, 0, -1, 0, -2, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.triangle 29 0, .triangle 34 1, .triangle 31 0, .triangle 19 2, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint fd1969d839eaf8079fcfb8963a5dfdb3b76dad9a61df94fde9f68f365b70e95b.
def localCycle00297 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 0, -1, 3, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 0]

-- Cycle fingerprint fd3532ae1aacb5835ff88740a60a432e82abb03dcaed3062aba332911ad97901.
def localCycle00298 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .distance 1 3]
    constant := ![0, -1, 3, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .triangle 20 0]

-- Cycle fingerprint fd3ba523112913f3a2c25a755f61b80b1e557224fc91d84f7ee00a3dec6ce484.
def localCycle00299 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint fe168f48d48af381052638b248b8be63bcf7b607be1b265a7edafc808bfd6f1b.
def localCycle00300 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint fe5c064b0b82065cdbf0b0c3bc0298a57e6c0be5e1ef811fcad5ced61d94e765.
def localCycle00301 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 20 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint fea3148e46417d2af82c27fece1bfb87428067b80f4efbe46bd218cb4c7a8bda.
def localCycle00302 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![2, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 24 1, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint fec7a78896ecf6b6f429b29dba2f7e397a65b7939f117860208fc951d5494d3a.
def localCycle00303 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 3, -3, 0, -1, -1, 0, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false, true, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1, .triangle 22 0, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1]

def library : Library := fun id => if id < 152 then (if id < 76 then (if id < 38 then (if id < 19 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 14 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)))) else (if id < 16 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))))) else (if id < 28 then (if id < 23 then (if id < 21 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none))) else (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))))) else (if id < 33 then (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)))) else (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))))))) else (if id < 57 then (if id < 47 then (if id < 42 then (if id < 40 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))))) else (if id < 52 then (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)))) else (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))))) else (if id < 66 then (if id < 61 then (if id < 59 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))))) else (if id < 71 then (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)))))))) else (if id < 114 then (if id < 95 then (if id < 85 then (if id < 80 then (if id < 78 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none))))) else (if id < 90 then (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))))) else (if id < 104 then (if id < 99 then (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none))) else (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))))) else (if id < 109 then (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))) else (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))))))) else (if id < 133 then (if id < 123 then (if id < 118 then (if id < 116 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))) else (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))))) else (if id < 128 then (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)))) else (if id < 130 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)))))) else (if id < 142 then (if id < 137 then (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))) else (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none))))) else (if id < 147 then (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)))) else (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))))))))) else (if id < 228 then (if id < 190 then (if id < 171 then (if id < 161 then (if id < 156 then (if id < 154 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none))) else (if id < 158 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))))) else (if id < 166 then (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)))) else (if id < 168 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)))))) else (if id < 180 then (if id < 175 then (if id < 173 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none))) else (if id < 177 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))))) else (if id < 185 then (if id < 182 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)))) else (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))))))) else (if id < 209 then (if id < 199 then (if id < 194 then (if id < 192 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none))) else (if id < 196 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))))) else (if id < 204 then (if id < 201 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)))) else (if id < 206 then (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none)))))) else (if id < 218 then (if id < 213 then (if id < 211 then (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none)) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none))) else (if id < 215 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none))))) else (if id < 223 then (if id < 220 then (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none)) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)))) else (if id < 225 then (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)) else (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)))))))) else (if id < 266 then (if id < 247 then (if id < 237 then (if id < 232 then (if id < 230 then (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none)) else (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none))) else (if id < 234 then (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none)) else (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none))))) else (if id < 242 then (if id < 239 then (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none)) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none)))) else (if id < 244 then (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none)) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none)))))) else (if id < 256 then (if id < 251 then (if id < 249 then (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id = 248 then some localCycle00248 else none)) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none))) else (if id < 253 then (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none)) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none))))) else (if id < 261 then (if id < 258 then (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none)))) else (if id < 263 then (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none)) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id = 265 then some localCycle00265 else none))))))) else (if id < 285 then (if id < 275 then (if id < 270 then (if id < 268 then (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id = 267 then some localCycle00267 else none)) else (if id < 269 then (if id = 268 then some localCycle00268 else none) else (if id = 269 then some localCycle00269 else none))) else (if id < 272 then (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id = 271 then some localCycle00271 else none)) else (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id = 274 then some localCycle00274 else none))))) else (if id < 280 then (if id < 277 then (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id = 276 then some localCycle00276 else none)) else (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id = 279 then some localCycle00279 else none)))) else (if id < 282 then (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id = 281 then some localCycle00281 else none)) else (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id = 284 then some localCycle00284 else none)))))) else (if id < 294 then (if id < 289 then (if id < 287 then (if id < 286 then (if id = 285 then some localCycle00285 else none) else (if id = 286 then some localCycle00286 else none)) else (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id = 288 then some localCycle00288 else none))) else (if id < 291 then (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id = 290 then some localCycle00290 else none)) else (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id = 293 then some localCycle00293 else none))))) else (if id < 299 then (if id < 296 then (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id = 295 then some localCycle00295 else none)) else (if id < 297 then (if id = 296 then some localCycle00296 else none) else (if id < 298 then (if id = 297 then some localCycle00297 else none) else (if id = 298 then some localCycle00298 else none)))) else (if id < 301 then (if id < 300 then (if id = 299 then some localCycle00299 else none) else (if id = 300 then some localCycle00300 else none)) else (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id < 303 then (if id = 302 then some localCycle00302 else none) else (if id = 303 then some localCycle00303 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 82 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18304)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 0, 5, 2, 6], ![1, 3, 0, 4, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 247 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18305)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 5, 0, 2, 6], ![1, 3, 4, 0, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 279 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18306)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 5, 4, 0, 6, 2], ![1, 5, 3, 0, 2, 6], ![1, 4, 3, 0, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 246 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18307)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 5, 4, 0, 6, 2], ![5, 1, 3, 0, 2, 6], ![4, 1, 3, 0, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 30 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18308)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 0, 2, 6, 5], ![1, 3, 0, 6, 2, 4], ![1, 0, 3, 5, 2, 4]], proof := .tail 19 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18309)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 0, 5, 6, 2], ![1, 3, 0, 4, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 288 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18310)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 5, 0, 6, 2], ![1, 3, 4, 0, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 56 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18311)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 4, 0, 6, 2], ![1, 5, 3, 0, 6, 2], ![1, 4, 3, 0, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 185 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18312)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 4, 0, 6, 2], ![5, 1, 3, 0, 6, 2], ![4, 1, 3, 0, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 41 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18313)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 0, 6, 2, 5], ![1, 3, 0, 6, 2, 4], ![1, 0, 3, 5, 4, 2]], proof := .tail 80 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18314)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 0, 5, 6, 2], ![1, 3, 0, 4, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 85 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18315)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 0, 6, 5, 2], ![1, 3, 0, 6, 4, 2], ![1, 0, 3, 5, 4, 2]], proof := .tail 12 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18316)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 5, 0, 6, 2], ![1, 3, 4, 0, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 51 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18317)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 4, 0, 6, 2], ![1, 5, 3, 0, 6, 2], ![1, 4, 3, 0, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 235 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18318)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 4, 0, 6, 2], ![5, 1, 3, 0, 6, 2], ![4, 1, 3, 0, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 79 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18319)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 0, 2, 5, 6], ![1, 3, 0, 2, 4, 6], ![1, 3, 0, 2, 4, 5]], proof := .low (![136, 211, 36, 98, 219, 282, 9, 103, 257, 286, 67, 158, 177, 87, 89, 178, 153, 142, 13, 294, 230, 17, 1, 101, 236, 21, 236, 236]) }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18320)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 4], ![1, 3, 0, 2, 5, 4]], proof := .low (![136, 211, 36, 261, 219, 282, 9, 103, 257, 286, 67, 158, 177, 87, 48, 178, 153, 142, 13, 294, 230, 17, 1, 101, 302, 21, 236, 236]) }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18321)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 0, 2, 6, 5], ![1, 3, 0, 6, 2, 4], ![1, 3, 0, 5, 2, 4]], proof := .low (![38, 74, 36, 15, 219, 282, 9, 220, 238, 216, 67, 195, 177, 228, 289, 178, 115, 142, 26, 182, 230, 17, 111, 101, 236, 21, 236, 166]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18322)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 0, 2, 6, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 0, 2, 4]], proof := .tail 275 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18323)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 0, 2, 6, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 0, 2, 4]], proof := .tail 209 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18324)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 4, 6, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 0, 2, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 0, 2, 4]], proof := .low (![64, 172, 36, 245, 124, 84, 112, 123, 207, 53, 249, 290, 183, 71, 258, 301, 152, 189, 25, 190, 95, 23, 210, 6, 187, 299, 169, 88]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18325)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 0, 6, 2, 5], ![1, 3, 0, 6, 2, 4], ![1, 3, 0, 5, 4, 2]], proof := .tail 65 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18326)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 0, 6, 2, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 0, 4, 2]], proof := .tail 65 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18327)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 0, 6, 2, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 0, 4, 2]], proof := .tail 65 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18328)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 0, 6, 2, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 0, 4, 2]], proof := .tail 65 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18329)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 6, 0, 2, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 4, 0, 2]], proof := .tail 62 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18330)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 0, 2, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 4, 0, 2]], proof := .tail 62 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18331)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 0, 2, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 4, 3, 0, 2]], proof := .tail 167 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18332)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 0, 2, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 4, 0, 2]], proof := .tail 62 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18333)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 0, 2, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 224 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18334)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 6, 4, 5, 0, 2], ![6, 1, 3, 0, 2, 5], ![6, 1, 3, 0, 2, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 285 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18335)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 0, 5, 2, 6], ![1, 3, 0, 4, 2, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 247 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18336)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 0, 5, 6, 2], ![1, 3, 0, 4, 2, 6], ![1, 3, 0, 4, 2, 5]], proof := .low (![212, 203, 36, 98, 219, 282, 9, 231, 222, 286, 67, 100, 177, 296, 89, 178, 229, 142, 29, 182, 174, 241, 1, 101, 236, 21, 236, 236]) }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18337)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 0, 5, 6, 2], ![1, 3, 0, 4, 6, 2], ![1, 3, 0, 4, 5, 2]], proof := .tail 85 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18338)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 0, 6, 5, 2], ![1, 3, 0, 6, 4, 2], ![1, 3, 0, 5, 4, 2]], proof := .tail 163 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18339)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 0, 6, 5, 2], ![1, 3, 6, 0, 4, 2], ![1, 3, 5, 0, 4, 2]], proof := .tail 163 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18340)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 0, 6, 5, 2], ![1, 6, 3, 0, 4, 2], ![1, 5, 3, 0, 4, 2]], proof := .tail 209 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18341)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 0, 6, 5, 2], ![6, 1, 3, 0, 4, 2], ![5, 1, 3, 0, 4, 2]], proof := .low (![268, 119, 36, 245, 124, 164, 112, 46, 31, 53, 249, 22, 183, 281, 258, 301, 137, 189, 262, 58, 95, 23, 210, 6, 187, 299, 169, 70]) }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18342)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 6, 0, 5, 2], ![1, 3, 6, 0, 4, 2], ![1, 3, 5, 4, 0, 2]], proof := .tail 265 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18343)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 0, 5, 2], ![1, 6, 3, 0, 4, 2], ![1, 5, 3, 4, 0, 2]], proof := .tail 265 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18344)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 0, 5, 2], ![1, 6, 3, 0, 4, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 204 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18345)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 0, 5, 2], ![6, 1, 3, 0, 4, 2], ![5, 1, 3, 4, 0, 2]], proof := .tail 265 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18346)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 0, 5, 2], ![6, 1, 3, 0, 4, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 77 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18347)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 4, 5, 0, 2], ![6, 1, 3, 0, 5, 2], ![6, 1, 3, 0, 4, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 154 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18348)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 0, 2, 6], ![1, 3, 4, 0, 2, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 81 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18349)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 0, 6, 2], ![1, 3, 4, 0, 2, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 56 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18350)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 0, 6, 2], ![1, 3, 4, 0, 6, 2], ![1, 3, 0, 4, 5, 2]], proof := .tail 51 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18351)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 6, 0, 2], ![1, 3, 4, 0, 2, 6], ![1, 3, 4, 0, 2, 5]], proof := .tail 139 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18352)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 6, 0, 2], ![1, 3, 4, 0, 6, 2], ![1, 3, 4, 0, 5, 2]], proof := .tail 69 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18353)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 6, 0, 2], ![1, 3, 4, 6, 0, 2], ![1, 3, 4, 5, 0, 2]], proof := .tail 42 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18354)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 6, 5, 0, 2], ![1, 3, 6, 4, 0, 2], ![1, 3, 5, 4, 0, 2]], proof := .tail 132 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18355)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 5, 0, 2], ![1, 6, 3, 4, 0, 2], ![1, 5, 3, 4, 0, 2]], proof := .tail 242 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18356)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 5, 0, 2], ![6, 1, 3, 4, 0, 2], ![5, 1, 3, 4, 0, 2]], proof := .tail 242 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18357)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 5, 0, 2], ![1, 6, 3, 4, 0, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 271 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18358)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 5, 0, 2], ![6, 1, 3, 4, 0, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 200 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18359)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 4, 5, 0, 2], ![6, 1, 3, 5, 0, 2], ![6, 1, 3, 4, 0, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 248 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18360)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 0, 2, 6], ![1, 4, 3, 0, 2, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 270 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18361)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 0, 6, 2], ![1, 4, 3, 0, 2, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 117 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18362)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 0, 6, 2], ![1, 4, 3, 0, 6, 2], ![1, 3, 0, 4, 5, 2]], proof := .tail 121 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18363)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 6, 0, 2], ![1, 4, 3, 0, 2, 6], ![1, 3, 4, 0, 2, 5]], proof := .tail 272 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18364)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 6, 0, 2], ![1, 4, 3, 0, 6, 2], ![1, 3, 4, 0, 5, 2]], proof := .tail 272 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18365)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 6, 0, 2], ![1, 4, 3, 6, 0, 2], ![1, 3, 4, 5, 0, 2]], proof := .tail 109 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18366)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 6, 4, 0, 2], ![1, 5, 6, 3, 0, 2], ![1, 4, 3, 0, 2, 6], ![1, 4, 3, 0, 2, 5]], proof := .tail 8 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18367)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 6, 4, 0, 2], ![1, 5, 6, 3, 0, 2], ![1, 4, 3, 0, 6, 2], ![1, 4, 3, 0, 5, 2]], proof := .tail 8 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18368)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 6, 4, 0, 2], ![1, 5, 6, 3, 0, 2], ![1, 4, 3, 6, 0, 2], ![1, 4, 3, 5, 0, 2]], proof := .tail 298 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18369)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 4, 0, 2], ![1, 5, 6, 3, 0, 2], ![1, 4, 6, 3, 0, 2], ![1, 4, 5, 3, 0, 2]], proof := .tail 297 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18370)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 4, 0, 2], ![1, 6, 5, 3, 0, 2], ![1, 6, 4, 3, 0, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 45 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18371)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 4, 0, 2], ![1, 6, 5, 3, 0, 2], ![6, 1, 4, 3, 0, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 75 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18372)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 4, 0, 2], ![6, 1, 5, 3, 0, 2], ![6, 1, 4, 3, 0, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 201 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18373)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 0, 2, 6], ![4, 1, 3, 0, 2, 6], ![1, 3, 0, 2, 4, 5]], proof := .low (![116, 55, 20, 63, 47, 303, 254, 60, 202, 44, 263, 291, 50, 3, 287, 16, 179, 260, 134, 218, 300, 250, 32, 28, 284, 37, 276, 171]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18374)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 0, 6, 2], ![4, 1, 3, 0, 2, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 125 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18375)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 0, 6, 2], ![4, 1, 3, 0, 6, 2], ![1, 3, 0, 4, 5, 2]], proof := .tail 79 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18376)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 1, 3, 0, 2, 6], ![1, 3, 4, 0, 2, 5]], proof := .tail 186 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18377)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 1, 3, 0, 6, 2], ![1, 3, 4, 0, 5, 2]], proof := .tail 73 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18378)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 1, 3, 6, 0, 2], ![1, 3, 4, 5, 0, 2]], proof := .tail 106 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18379)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 1, 3, 0, 2, 6], ![1, 4, 3, 0, 2, 5]], proof := .tail 157 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18380)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 1, 3, 0, 6, 2], ![1, 4, 3, 0, 5, 2]], proof := .tail 157 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18381)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 1, 3, 6, 0, 2], ![1, 4, 3, 5, 0, 2]], proof := .tail 157 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18382)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 1, 6, 3, 0, 2], ![1, 4, 5, 3, 0, 2]], proof := .tail 264 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18383)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 1, 3, 0, 2, 6], ![4, 1, 3, 0, 2, 5]], proof := .low (![91, 259, 20, 295, 233, 140, 61, 251, 161, 188, 118, 162, 151, 180, 223, 176, 143, 120, 131, 244, 217, 266, 59, 18, 280, 99, 129, 135]) }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18384)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 1, 3, 0, 6, 2], ![4, 1, 3, 0, 5, 2]], proof := .low (![91, 259, 20, 295, 233, 214, 61, 251, 102, 188, 118, 162, 151, 113, 223, 176, 143, 120, 256, 149, 217, 266, 59, 18, 280, 99, 129, 283]) }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18385)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 1, 3, 6, 0, 2], ![4, 1, 3, 5, 0, 2]], proof := .tail 298 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18386)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 1, 6, 3, 0, 2], ![4, 1, 5, 3, 0, 2]], proof := .tail 114 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18387)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 6, 1, 3, 0, 2], ![4, 5, 1, 3, 0, 2]], proof := .tail 243 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18388)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 4, 0, 2], ![6, 5, 1, 3, 0, 2], ![6, 4, 1, 3, 0, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 198 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18389)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 4, 5, 3], ![6, 1, 4, 5, 0, 2], ![6, 1, 3, 0, 2, 5], ![6, 1, 3, 0, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 127 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18390)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 4, 5, 0, 2], ![6, 1, 3, 0, 5, 2], ![6, 1, 3, 0, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 205 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18391)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 4, 5, 0, 2], ![6, 1, 3, 5, 0, 2], ![6, 1, 3, 4, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 107 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18392)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 5, 4, 0, 2], ![6, 1, 5, 3, 0, 2], ![6, 1, 4, 3, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 267 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18393)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 3, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 5, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 6, 1, 3, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 93 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18394)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 3, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 5, 4, 0, 2], ![6, 5, 1, 3, 0, 2], ![6, 4, 1, 3, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 0 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18395)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 4, 3, 6], ![5, 1, 4, 0, 2, 6], ![5, 1, 3, 0, 2, 6], ![4, 3, 1, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 108 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18396)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 4, 6, 3], ![5, 1, 4, 0, 6, 2], ![5, 1, 3, 0, 2, 6], ![4, 3, 1, 0, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 5 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18397)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![5, 1, 4, 0, 6, 2], ![5, 1, 3, 0, 6, 2], ![4, 3, 1, 0, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 144 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18398)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 4, 0, 6, 2], ![5, 1, 3, 0, 6, 2], ![4, 3, 1, 0, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 35 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18399)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 4, 6, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 0, 2, 6], ![4, 3, 1, 0, 2, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 90 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18400)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 0, 6, 2], ![4, 3, 1, 0, 2, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 66 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18401)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 3, 1, 0, 2, 6], ![1, 3, 4, 0, 2, 5]], proof := .tail 4 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18402)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 3, 1, 0, 2, 6], ![1, 4, 3, 0, 2, 5]], proof := .tail 97 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18403)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 5, 6, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 0, 2, 6], ![4, 1, 3, 0, 2, 5]], proof := .tail 168 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18404)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 0, 6, 2], ![4, 3, 1, 0, 6, 2], ![1, 3, 0, 4, 5, 2]], proof := .tail 160 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18405)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 3, 1, 0, 6, 2], ![1, 3, 4, 0, 5, 2]], proof := .tail 160 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18406)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 3, 1, 0, 6, 2], ![1, 4, 3, 0, 5, 2]], proof := .tail 97 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18407)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 0, 6, 2], ![4, 1, 3, 0, 5, 2]], proof := .tail 168 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18408)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 3, 1, 6, 0, 2], ![1, 3, 4, 5, 0, 2]], proof := .tail 232 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18409)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 3, 1, 6, 0, 2], ![1, 4, 3, 5, 0, 2]], proof := .tail 97 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18410)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 6, 0, 2], ![4, 1, 3, 5, 0, 2]], proof := .tail 168 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18411)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 6, 3, 4, 0], ![1, 0, 5, 6, 4, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 252 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18412)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 6, 3, 4, 0], ![1, 0, 6, 5, 4, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 5, 2]], proof := .tail 252 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18413)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 5, 6, 3, 4, 0], ![1, 0, 6, 5, 4, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 0, 2]], proof := .tail 252 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18414)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 5, 3, 4, 0], ![1, 0, 6, 5, 4, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 83 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18415)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 5, 3, 4, 0], ![1, 0, 6, 5, 4, 3], ![6, 5, 1, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 33 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18416)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 5, 3, 4, 0], ![1, 0, 6, 5, 4, 3], ![6, 5, 1, 4, 0, 2], ![6, 5, 1, 3, 0, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 208 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18417)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 1, 0, 2, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![227, 27, 197, 94, 155, 14, 193, 86, 150, 148, 43, 128, 173, 239, 11, 237, 278, 72, 52, 221, 225, 76, 213, 292, 240, 21, 34, 104]) }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18418)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 1, 0, 2, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 54 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18419)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 3, 5, 6], ![4, 1, 0, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .low (![181, 27, 197, 145, 138, 14, 193, 86, 150, 148, 133, 156, 173, 239, 191, 2, 278, 72, 68, 221, 225, 76, 213, 277, 78, 21, 147, 269]) }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18420)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .low (![24, 27, 197, 145, 138, 14, 193, 86, 150, 148, 133, 126, 173, 239, 191, 2, 278, 72, 68, 221, 225, 76, 213, 234, 78, 21, 147, 104]) }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18421)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 165 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18422)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 4, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low (![96, 274, 197, 105, 124, 40, 175, 159, 130, 122, 57, 226, 39, 92, 206, 196, 199, 215, 273, 255, 141, 253, 110, 170, 49, 299, 192, 88]) }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18423)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 3, 2, 4]], proof := .tail 7 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18424)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 3, 2, 4]], proof := .tail 7 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18425)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 4, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 184 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18426)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 3, 4, 2]], proof := .tail 146 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18427)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 3, 4, 2]], proof := .tail 146 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18428)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 10 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18429)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 6, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 0, 2, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 0, 2, 4]], proof := .tail 194 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18430)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 0, 6, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 0, 4, 2]], proof := .tail 293 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18431)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (18304 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 18304 ≤ id.val) (hhigh : id.val < 18432) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 18304)) = true := by
  let j : Fin 128 := ⟨id.val - 18304, by omega⟩
  have hsum : 18304 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (18304 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard143
