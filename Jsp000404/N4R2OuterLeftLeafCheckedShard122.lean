import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard122
open N4R2OuterLeftReplay

-- Cycle fingerprint 0128ff1bf3675291abfd956886cd8ae83d9cd61a75dc4cdae86ba47372c428af.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4]
    constant := ![0, -2, 0, -1, 0, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 22 2, .gapLower 1 4, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 21 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 026806e1c3a256020c772d1dc1cd8b5c01201a9fd45fec865d5206ea86b9cacf.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 02898992dff1d8e913de3e1f1b970d0d1f14e8a05ba7c6234e270b52b8e42976.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 02fce07ceb35478566a6ea47d42a25f3f3708891290f586522ca05a571fa50c8.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 6]
    constant := ![0, -1, -1, -1, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 8 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 4 2]

-- Cycle fingerprint 0412fdca986565b831055c22f45a4944654fcdc67ebbb86c624069c566b4207e.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 0441a4542de19927e8c59c23105a8ca9dc5526bd73e4e1cefb423bb5f11f25e3.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 1 3, .theta 1, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![-2, -1, 4, 0, -2, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 0 2, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint 0480d88873ab7bb860b0678510515e27902b8e06515a9c2a6de5e2869ffd8559.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -1, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.triangle 8 0, .triangle 27 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint 04c7bc83f6f7aeebb25cf90ed40717774dc7d92d012dbf884c9fb8269d5da125.
def localCycle00007 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .theta 1, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 0512dc5c2ebd057c9bdf33dbe556d9abeef510372ddfefa49ca39347dddd1d53.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 05bed85b0c06f6059c1232f6953c9e19e8b01977ea6d0abc6c9ae355a16da4d5.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 0616feca516de02a1ac00807448d7771767ef53fd2cdec9ebfdc899f21c4a32f.
def localCycle00010 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 18 1, .gapLower 1 0, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 0703fa48038387ff07c191a33c10de267b3125784b4116154158bc5db1f41da2.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, 0, -1, 3, 0, 0, -3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false] }
  origin := ![.gapLower 0 3, .triangle 7 0, .triangle 17 2, .triangle 22 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 0825efae243a5ce07249c4570bf75c3f422d3964e6ff332c8bbb08fed4a160f1.
def localCycle00012 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -3, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 08a8197b1a00e5349fee316a7971bc7016e367626ccd863159c02c37cca240ee.
def localCycle00013 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -1, -1, 0, -2, -2, -1, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 08fd98350f2f8edf8241bf204f4017092e6707a3e2c94bbfce83204514ee7dd5.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -1, 0, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 0 4, .triangle 8 0, .triangle 30 1, .triangle 17 0, .gapLower 1 0]

-- Cycle fingerprint 0b34cf70e6a581cd2bc4da75f6236d448d022e222d6ffbbc591c88bdad38e1dd.
def localCycle00015 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 4, .triangle 0 2, .gapUpper 2 4, .gapLower 6 3]

-- Cycle fingerprint 0c5357b90b2770cdcbbf23203e29fe8ef12d2cf7a0b7466b72b8240d7b097e7a.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 0 2, .triangle 5 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 0d694474d1872918f06cfc6f521610d52f41642ee642d6a111fce902884d6bcd.
def localCycle00017 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![0, -1, -1, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .triangle 7 0, .triangle 17 0, .gapLower 1 0, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 0e084fc094ef9904a383a0027a58512b5e812fbfdfd0416f9e9bbe1fb0f05264.
def localCycle00018 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5]
    constant := ![0, 0, -2, -2, 0, 0, 3, 0, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, true, false, true, true, false] }
  origin := ![.triangle 17 2, .triangle 20 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .triangle 8 1, .triangle 7 0]

-- Cycle fingerprint 124403293af4c8a4a4fbe90c208a33f253f72888989aae449a9538232e2fd251.
def localCycle00019 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2]
    constant := ![-1, -1, -1, 0, -1, 0, 0, 3, 0, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.triangle 5 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .triangle 8 1]

-- Cycle fingerprint 130e0087d20996e2b12f4606b79dc9d9b0ec88dc0369aacea5abd2c58616fceb.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5]
    constant := ![0, -2, -1, 4, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 17 2, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 8 1, .triangle 7 0]

-- Cycle fingerprint 136b4cb022c8f85c8dee1639a2edcf2499a95b2a71f077074468a858a0ccf04b.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -1, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 27 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 3 0, .gapLower 0 3]

-- Cycle fingerprint 140f692ef537cb98d58298f173648b36915d843547a746cf981a4781d276e1d9.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 3 2, .triangle 7 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 16c7c021752a604ddeb84c9aee2f25f310ad0c7ca491f48aee55faec17e4ccbb.
def localCycle00023 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 177df180315ee2bc2eead86f7693c738f057c25c6e7b196b135851c0abe68568.
def localCycle00024 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 18 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 178dd6454b203f4baaa2bb9b7ab91b3c211d2063de502948dfb9c3280f79223f.
def localCycle00025 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint 1802b3c8d10f82e6cb52a32dd4fdb3f1e800fa5921ab4d1f9ee34eb77d641b6d.
def localCycle00026 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, 0, 0, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 4 0, .gapLower 0 3, .gapLower 2 3, .triangle 26 1, .triangle 15 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 195eca79666434868369e2b13f4270b7912b3e1361097080006ecfa937d2edcd.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 1da6305a5d400f211ec94f752bfcf8859e95740c97560668fcba3b6576739509.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 1f55457217bb7af6b7f81b95eeb8cb01327024e71318080dfd9c5189b7d47907.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0]

-- Cycle fingerprint 1f930fb5faef108014811bf0bd8a370dcf5b30e08f636980d57f4389914f292b.
def localCycle00030 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 0 3, .triangle 7 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 210a011d9861f5fa5ed57662358b534a09504c89d39b858165fbb8d417472471.
def localCycle00031 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, 0, -2, -1, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 0, .gapLower 0 2, .gapLower 2 2, .triangle 15 0]

-- Cycle fingerprint 211e44acf98555d7e8614f32141d9d3653d73e87d89dd9a78d58fcc05fe88959.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 0 2, .triangle 5 0, .triangle 15 0, .gapLower 2 0]

-- Cycle fingerprint 226e5d6dbe4398dcdfbe9fb27f233fd150bb678ca5b6e6ca16b74f54502a4c01.
def localCycle00033 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, 0, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 5 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 23b0c8e71fe70ee6ccee72aa82694114c3775a1c4785e843fef43f0936236306.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, 0, -1, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, true, false, false] }
  origin := ![.triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 22 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 2436fbf8f0f78ba0859bc574e7ee315ce73b58b7151b1b68b2532c56651fe6de.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 247fab77695a71ee22dea1de3ea982fb9e219966351e4f9b1fa27e13974cd41a.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 251af2cf59e897727ffd21a8798cd1c3e24d66fe2c8acfb1825079ec5954c2ec.
def localCycle00037 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, 4, -1, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 2 0, .triangle 4 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 27107d9c8a99afcab8408a7389fcd31ed19b53fe09e4b91a4a64805b2d72f1cb.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0]

-- Cycle fingerprint 2814113dec7e8f3ba22674e5f69fd4455e348224aa4f5b9f1b9c1d423163a80a.
def localCycle00039 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .gapLower 1 3, .triangle 0 2, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 282e3ae97e15a813471f280756cd52e32e47cb38c8bce914f6a133198d84123d.
def localCycle00040 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 293d6a9359d3a99d2f216acf97f7b1624b902a1739554360a6b71f7735fda343.
def localCycle00041 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 29fb8da62a28cd80cb050754f167822ccb82ea357027ae3644873d1b54dff1df.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6]
    constant := ![0, 0, -1, -1, 1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 30 1, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0, .gapLower 0 4, .triangle 8 0]

-- Cycle fingerprint 2a3cbbf77393a2ccd61027d71cbd4175d137e73a069cb672bc35e1dbbcbb4b09.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 2bbf8826461ed9f3d3b956f7a08d2b3e22006d1eb7da6fb0c0ddd5b05f3a26c8.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 2c7a8b203f5e930f3e15d8e1f5dde8287b8e547e86591d6f18df7bfbf1600bb7.
def localCycle00045 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 2d11a415d2f40db9809e047fd64b9f1d249d584545134747583b574a76780d64.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 30cab73f81ad9c085dfc09398131bdce5b65f5776a1501b97d27bb209515b056.
def localCycle00047 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5]
    constant := ![-2, 0, 0, -1, 0, -2, -1, 0, 0, 0, 3, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false, false, true, true, true] }
  origin := ![.gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 5 0, .triangle 15 2, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2]

-- Cycle fingerprint 336b59420a2e659b178441175c930f26636bfa91207a9f0af30a1e3ff1e7dba4.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 3, 0, 0, -3, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 34 0]

-- Cycle fingerprint 33c843139e28051488d460a2a88a13735c2eb64786a21226b5c9517f1d48ebea.
def localCycle00049 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 1 4, .distance 0 1, .distance 1 6]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 349eeb80eb2ec711237b9448f809234c5b89e081d08e767203ce3ba4c2c15e61.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 36c251a2192c463a7e55ff7c6b69c36c8e172caca02f46525ffd86360d28a751.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 36ee0ee14963cc5789f74c78921ad3b05b1f5daec0f5350ffa58c16c89371c6f.
def localCycle00052 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .triangle 24 0, .triangle 14 0, .triangle 3 1, .triangle 0 2, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 38c5178d34a6be778456575df03ba68c6604f10c5254e7c6cabf171ed4dd6a37.
def localCycle00053 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 2, .triangle 22 1, .corridorLower 4 5]

-- Cycle fingerprint 39ac4d0c63665c66aba3488e8b03707ac9a719955551c0688d10479071703574.
def localCycle00054 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 21 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 3a9ad37a73064c7dd9c930c8061a8b7437c1d440991b3abc1fc9df4621313e51.
def localCycle00055 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 3acba21eeb4d86adbe0fbbc030b15a704f0341faab5b7bae4c0185cd244f8066.
def localCycle00056 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 17 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 3b3967152d16adc3ccf8065f68aef5be3d0ef06bb66b32c1eaaecf6b47880b57.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 3c5cffd6e2f247e69f14befccd8eb817b84952f56a13e75968afe85a3ed9124b.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![2, -2, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 3 0, .gapLower 0 2, .triangle 5 0, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 3d023ab631dab76f56d6d2f62465ad4ddf82f185ea6e6ff25a2f86b1aa979ae4.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -3, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 4 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0]

-- Cycle fingerprint 3dcf74bb0225a0c7965de799a7dac4204e6c47b16f13c30bc80ad97535fdeecd.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 4 2, .triangle 8 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 3f0dcbba987a1ff3be9dab1e0ab5f8dd200d331fab97bb5b8d53e1e8898ba7f8.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 3f3e1d76a29a4f188d9c9d04b665d3cbe7140037973166b37f0f1ee896ade9ee.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 0 3, .triangle 8 0, .triangle 27 1, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 4045793744a948b8f148b1381e5858f78958c857871af4c3fbc1ec37793e05de.
def localCycle00063 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 4215e569ed7cfc4cf8bba82958735efa2ed0476a48f36ef245e2a3b06beb9e64.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2]
    constant := ![-1, 0, -1, -1, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.triangle 7 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 8 1]

-- Cycle fingerprint 4229a1f996d6bdd3bb0aac43090dd88808ce5f23bc4ad2081f0139b4d6f06522.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 4295af409eec301b707b6267b8a5ccceac86fa19b38bac59ab05f1be61b478ea.
def localCycle00066 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .theta 1, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![-1, 4, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 2 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 430746d4c6eced535f1057a7d06506d4582823a116f50554d10753b4a401afb1.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 432e9cec5d74b7c595d9980849de10fc6a99cd82bead7675047d15bdf3a35bed.
def localCycle00068 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 7 1, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 44375e4f4f104d8e6069ee562b8660ddfa30a1cdddbe8d00289e5987f7e5f5c8.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 46082b814d2d15a0e59b113d46668847de5eaa1ad6553cc38c21166f70342743.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4]
    constant := ![0, -2, 0, -1, 0, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 23 2, .gapLower 1 4, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 47630d6f79611af0010ea4cf57d90d545f85b8647477aec16822bb789a5811fa.
def localCycle00071 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 484c175b5eee2deeedf380084dbf5876609085721a2c516fdee00dc3cd608ac6.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1, .distance 1 6]
    constant := ![-2, 0, -2, -1, 4, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0, .triangle 4 0]

-- Cycle fingerprint 49a5695d208af5ec18711407a9716cefb1048d65ee5ed346f97ec699aa8304ad.
def localCycle00073 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 4e7241a147f58f915d540e7a4238e37bad2b5bed214cfe60c1a5d6a421c6a818.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 4e7cf59c9728d3e94676a4f4db728403ab542383997b149d96bf016d19e1b83d.
def localCycle00075 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![0, 0, -2, 0, -1, 0, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, false, true, false, false, false, false, false, true, true] }
  origin := ![.triangle 22 2, .triangle 24 2, .gapLower 1 3, .triangle 0 2, .triangle 5 0, .triangle 15 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint 4f0374b7de66e6b70d8343bef52a02d785543f60320ddbb962f9db6b2fff4993.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .gapLower 1 3, .triangle 22 1, .corridorLower 4 5]

-- Cycle fingerprint 5185a5e1f946927e1d7f44f36bf62a2f476179f9137717e3c12aff42cb94af3c.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Cycle fingerprint 51b14c48b48dbb846984c5a31ed77dbad6e80a6fad99d7bc728785777f61b82d.
def localCycle00078 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 52d7f5561139b4d68d89cb65c372fe773be2354ceb2134ca904d51a47a2562c8.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2]
    constant := ![-1, -1, -1, 4, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 5 0, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 0 2]

-- Cycle fingerprint 5446e7eb20ce415c6344aa7ddb2948ab52eb5f27d55d4a51380b5b0e9e093b68.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2]
    constant := ![-1, 0, -1, -1, 1, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.triangle 7 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0, .triangle 4 2, .triangle 8 1]

-- Cycle fingerprint 5514a5d05e2c3f32ee6412391cdc90f8b9cb7176cba943f1d17eaf71ec7f1087.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4]
    constant := ![-2, -1, -1, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 0, .triangle 4 0, .triangle 21 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 575f3a2d8b3f8e3c1415eee792b9b4361fe46463c5443b5fedfb72e4022ee5e0.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 57b130258365dddb1211b0fda8c16a3ab99b90c60ff51519d8b3e85a139b141b.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -1, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 4 0, .gapLower 0 3]

-- Cycle fingerprint 58f7c2b31e660e3327c094f25d7b423c8b0d998dbf774c875cb5ea6864686236.
def localCycle00084 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 59bdb45b5bf84960f43bfff1ebf84594daa3befbd72773db0bb84f4ccedef066.
def localCycle00085 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 5b9c347da0bbd8e852505b3581242a1e8c372a9e5280e789d6eaf38eeca59e87.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 5cb1e95093801411af83014f25a2d9cc20c71fe738cff94d84ccf5b73a32695f.
def localCycle00087 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 5ee4aa0a154ad691cabebe8fae15c7d8bf15a83451b4f750d9122d0e188a2861.
def localCycle00088 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 3, .theta 1, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 655cc0dbcf9fc4c14ad1cd67b2f0ac7252519ae3c5769ac5e83a479d68a19465.
def localCycle00089 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 65d85f41b7f0ece631eade9756980b63bcb7ca0457dc4b12687520255950ea1b.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 6, .distance 4 6]
    constant := ![-1, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 6, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 0, .triangle 4 0, .triangle 23 1]

-- Cycle fingerprint 685eb9419570f43535c426ea931ce48991cbff510ba674e2aea04489df25a129.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6]
    constant := ![0, 0, -1, -1, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 30 1, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 0 2, .triangle 8 0]

-- Cycle fingerprint 68b4b72b733c25054b9717778228ea242df71f4fabefd09aa061b5e7f2ceef39.
def localCycle00092 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 6a754d891a96ade271f0073a0d8232b99bdc54672ee3b5c94d2b07aeaaf8b7ac.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 5]
    constant := ![0, 3, 0, 0, -2, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 34 0]

-- Cycle fingerprint 6bc0a1b860df28571bcd61e8d1dfbf275e728ce32021f54596c520fdfe9c39bf.
def localCycle00094 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 6c2e272062cd8dc9246c6c0a368c0eb531fbd9c1e3d0fdc1ef215fddaa2c7b88.
def localCycle00095 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, 0, -2, -1, 0, 0, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 4 0, .gapLower 0 2, .gapLower 2 2, .triangle 15 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 6c2eaf8ab59dba1634545f6d5e37ab78a9b5c16466588940d26612a14e074a9b.
def localCycle00096 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .triangle 4 0, .triangle 3 2, .triangle 7 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 6e0389b51a0b852b7b78c7940bccde62c1b6877521c046483700629bbb736c08.
def localCycle00097 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 4 0, .gapLower 0 2, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 7028f2b6d2a0f15aae5136aded3a3b167f8152c46211d8f172c0221806fc3f0c.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 72db1251bec9e055eaf4323456a320a4548c16a7ee29dbbefaee10b2258dc2fa.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 3, .distance 1 2, .theta 2, .distance 2 4, .distance 2 5]
    constant := ![0, -3, 0, 0, -1, -1, 0, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 5 0, .triangle 15 0, .gapLower 2 0, .gapLower 2 6, .triangle 28 2]

-- Cycle fingerprint 7305cd2d9d6de00bb6f39d3d7c68443a6d8b398e4d9c6e42e23aca339eaac89d.
def localCycle00100 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1]
    constant := ![0, 0, -1, 0, -3, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 17 2, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0]

-- Cycle fingerprint 735e73e9ae428bf25da6f1ad5a6935ca56aab1e17e7b6b5d028dba34c897a225.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 22 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 73c36b78d5ee38e1d2a3be72ca1fcff632c576a9661f302e0853b8745cd9c717.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, -1, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 74df74e005fc6836379459a7132dba8c4edd4c7df106d537ae8b424f67b992a3.
def localCycle00103 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Cycle fingerprint 7627b3972a4f9a27d93115eb94b296cf190b8b3c0d102e7f198258a1af755b91.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Cycle fingerprint 770f092b56924710a858de1ecc75a90a225ec6b0814f32f006e332783265553c.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 30 0, .triangle 17 2, .triangle 22 1, .corridorLower 4 5]

-- Cycle fingerprint 7745b715fcef4e85a97dc9d389382e387dfe5fa958aea8fd254384b0998d70b1.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, -1, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 21 0, .gapLower 1 1]

-- Cycle fingerprint 77c09f9c89579fee8d098a443da48f740402de9983594830d242bb77d08c46d6.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 21 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 77f90673bfcf821d3c26de7214efccb52fa4cb9288c8e340a7dfdc54f3c2337a.
def localCycle00108 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 780d00ff99a5f2e02fb429bef7512bbb41432de746ea38e55345539c7a499ebe.
def localCycle00109 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 79194aa717593b10c8091c083ddfbee14a25ec3035b9848b9cd29ef8c52c3187.
def localCycle00110 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 7ac28247c9ebe1fbad0c2d41627a36bf2b346eb4b221ae3be300ddc745f4999e.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6]
    constant := ![0, -2, 0, -2, -1, 4, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0, .triangle 0 2, .triangle 8 0]

-- Cycle fingerprint 7b482343d3510dab56d183d392a310991b5ee4eab56342f019ff64b5df9e7807.
def localCycle00112 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, 0, 0, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 0, .triangle 4 2, .triangle 8 1, .gapLower 2 2, .triangle 15 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 7cb574f54f81fa3e10d71bcfda84097f8b5755c63ae99c67ca939285435810c0.
def localCycle00113 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7da75828db088badb6246d4c33aa7d663fdf644454b0d374caa5cefd8fe7041d.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![0, -2, -2, -1, 4, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0, .triangle 0 2, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint 80ae4b8c90481fb34e82147120e2eaabfc8cfb77c06d8dbfe80dd10094319602.
def localCycle00115 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, 0, -2, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 20 1, .gapLower 1 1]

-- Cycle fingerprint 82d0e0c424e0700e6e8e28ac62bca0721dcb16a423778b12790f9d25c2ff1610.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 82e9666f8e440b89b5c6cd7d9ed4080ba55ead52dec81d2718e0d51b51e1816e.
def localCycle00117 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 832611386cb6392dcfb690d390372a6f149d8691967481b0ad45f9815c92429a.
def localCycle00118 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 4, .triangle 0 2, .gapUpper 2 4, .gapLower 5 4]

-- Cycle fingerprint 833afcee5456b98b03b68a3c5748bca445172caa42997b08d7ffe47752cbbd6d.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 84ef82ef5e5685e82395ce3c7aca527e6f7c4bf29d87bc5df7f1dcaa0eb2a61f.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 5]
    constant := ![-1, -3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1]

-- Cycle fingerprint 854207b409da32ac257b7030c2898a1134af9f18ea677759c11677242624c50e.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, -1, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 17 0, .gapLower 1 0]

-- Cycle fingerprint 86fd0f0eb886b19cca435b4c601d981451c558b8f7d47e6c54dd94026157b64f.
def localCycle00122 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![4, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 4 0, .gapLower 1 3, .corridorLower 1 5]

-- Cycle fingerprint 8789ca7bdd4acc43bb2e0be77a61004f4730fb6aedae091938569b8dd0606c5d.
def localCycle00123 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 87af9d77a3b92f11c5119d9381685d7384d3d940b0183de4a0a1df4679ac1091.
def localCycle00124 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -2, -1, 0, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 4 0, .gapLower 0 2, .gapLower 2 2, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 88b8706a971645d9cc30ce6ae3f746fc992251e469fd045f56b42435fbae472b.
def localCycle00125 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 89f670deb223630c57ee250822e8137eeb0f126267be8aee45084d8531965a6d.
def localCycle00126 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, 0, -3, -1, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 0, .gapLower 0 2, .triangle 5 0, .triangle 15 0]

-- Cycle fingerprint 8d5b69616b8769839a0eaa2cb770cadbf20ef82bbf259064d1f060d7d78a1750.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 8eb95c9a9eea11fe4ab1eb449b081b68c5625c56fac1c9b11a2621a599396a29.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -1, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.triangle 7 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 23 2, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint 8f1064f8d3be493460a47f0f18db1b9ab1c84bf58e425666a1a11c542c48089e.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 9097b3bf67c2f88e519bbefb6edef9260d469a9caf8692a003d6e0afa6d1842e.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 9125ea716f851a477f92875dd2ba963e6378c2a52a221fa00de204d2bba8deed.
def localCycle00131 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 93344deda0c95845937a8788d0f29def1ed1144f2e72a9b05a5c4cf4d58ef9c1.
def localCycle00132 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 2, .triangle 4 0, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 9606a3f739b32997e40e2ba5c5451488ac679949851c3e8c1cb77981387b7f78.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 974d2c66fa249fa0cbb2c05d6ad2eaaf16e78e756b3d41bc0fdbfcbc4ab91179.
def localCycle00134 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -1, 0, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 0 2, .triangle 8 0, .triangle 30 1, .triangle 26 1, .triangle 15 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 98dc341cd48230386aaa38e74004f978926b8ae832191e45d5e8c30e05332ef1.
def localCycle00135 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -1, 0, 0, -1, -1, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .triangle 2 0, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 99539a2251145764df0573ce788175f9b028488d005e33098f7cb26beffcb865.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![0, -2, -1, 4, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 0 2, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint 9b2dbb6241000ef34f6b40657afdab8f31c94a1d2800763b1db3ac103b1fa704.
def localCycle00137 : Cycle where
  length := 13
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 7 1, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 9b928ed718d16aecd6889007a8b2a702d083d4880b906a7cffd25f6bf292959e.
def localCycle00138 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![0, -1, -1, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .triangle 8 0, .triangle 18 0, .gapLower 1 0, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 9d2f28558e2aaf551afff09b69a0355de8298f833fbcc59ed8d7bd1bbffd0126.
def localCycle00139 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -1, 0, 0, -1, -1, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .triangle 2 0, .triangle 4 2, .triangle 8 1, .triangle 5 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 9d457ad25b18da9ca71052e4abf3082032da758f59fe9d049860de7fc7f37ce2.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, 0, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .gapLower 1 3, .triangle 22 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 9e2fddd43aa57fc77c2e8ca80c3092b1b17f6b4dcaf618353ddff446d7c70eee.
def localCycle00141 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -1, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint a04d3b7a6d609f4509f5a10b183c6691357ad3bec90992fcc0a94cd7e39861af.
def localCycle00142 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 0, .gapLower 0 2, .gapLower 2 2, .triangle 15 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint a2b2f559c8f454827d50280f0f76a3fcf2df36f76990192fe68773088cd96a4f.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint a41fa6fc9bd002eb1bab8e9abb6545bf907c49f233684888965d0baf1c586f92.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint a448d3adb6156aa17354556f5ec6f93d942df07af333696d41acfd33ddcb57c2.
def localCycle00145 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 2 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint a6ee551ad4119734be0ec07bbc9ada7ac46f29c80b37f6b0a74cb8e26555a6b3.
def localCycle00146 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .theta 1, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-1, 4, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 2 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint a7316dc1c402eb6272bbe0c9f178d539306b10799705fa42b91b914676aff8ef.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2]
    constant := ![-1, -1, -1, 4, -2, -2, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .gapLower 0 2]

-- Cycle fingerprint a7de5df3bb3a2bb1b6879507ec9ef9eb8e97482fb48b37e88eacaaa69e5f4cc2.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint a835d02e18580f1b7f57dd50d3035cce5a04c65ee18e5f1632a25d9cd59d9439.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint a91964e4cd6cfb220b5f928592f4c1067b17a563b760b633b72d20c2a832a922.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4]
    constant := ![-1, 0, -1, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 0 2, .triangle 8 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6]

-- Cycle fingerprint a97242a8655408125a21c49a9d8fa351374270199ac19bb8330bda1b4cbdca4b.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 4 5]
    constant := ![-1, 3, 0, 0, -2, -2, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 23 1, .triangle 34 1]

-- Cycle fingerprint a974a52d1314e8ca305888f389f05b444600ec10e3078dfcea5df45e1fd1276f.
def localCycle00152 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint a9c6f1bc783b2093f26e67558262be86eefd2c2b8292784356ccfe25c7b8a91d.
def localCycle00153 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -2, -1, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Cycle fingerprint aa7839fb9dc814bc168e5d66ad0c4cc94bc00d0ecbf332c4f559b40ad4692a7f.
def localCycle00154 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0]

-- Cycle fingerprint aa98e9cdf70ec0a263ad5c3b74c2493d0b40e846db77f7ce4aad2dd563b94fd1.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Cycle fingerprint ab5b2a9c6057a41b3989e5ef1765f5c586a651d19b415cbdf618601e0a80d5bb.
def localCycle00156 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint ac52088406b17996a5bdb5804ef4a8727316056eec1de7ab4052b6aa4f83a81b.
def localCycle00157 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 3 1, .gapLower 1 1, .gapUpper 2 1]

-- Cycle fingerprint acfe0874e157d9a1871b22ae471c428635236d05acd0555688f9d36cd2f7e768.
def localCycle00158 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 4 0, .triangle 24 1, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint ad7d244c30b893557c49a61e2c186bc2da55073c81101ca34e78bee3acce6da2.
def localCycle00159 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 0 2]
    constant := ![0, 2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 5 2, .gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 0 2]

-- Cycle fingerprint ae918daa158ad19c3a20b18dea810c909b281d75a5b12169a1f06fc5310355a8.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint af67fea681b9e91eb740eb49c6b395f56ae05468cb56b46c839e807c60a91dbc.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 6, .distance 4 6]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 6, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .triangle 23 1]

-- Cycle fingerprint b0746369f46b1f811b26c199f46d782217d4f5ba0c30f114860efe6913bd9b67.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 2, .triangle 23 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint b0f0028876c799210c1d9f576ff8a8a199666cfedbf94a74a88ea4c157539a9a.
def localCycle00163 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 22 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint b29732b0ca9d090842cca124ed5a463cd36098895ce4071bcaa5ff0d57b8f44d.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, -1, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2, .triangle 24 2, .gapLower 1 3]

-- Cycle fingerprint b369d8bf7a55a8bacbfb75b63d26f088c3f7e701196881ae894242b559aaf3b2.
def localCycle00165 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint b40327aaa0c94857cd7506de91be0817854a49ba9e7a9c45015253d541f2c796.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6]
    constant := ![0, -1, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 30 1, .triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0]

-- Cycle fingerprint b491e5d37577f98ada543cdcf72f485164477605b2b83a19ceaf967569fbca96.
def localCycle00167 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 0 2, .triangle 5 0, .triangle 15 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint b577f55aaa9c5f74296e06e66e9960534e153e3e23b107884671c8352caca1f5.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![4, -2, 0, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint b622e3202b2b5b5121b78c39cef9afa84a45d496ea74286e01eb9aa6608676f1.
def localCycle00169 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, 0, 0, -2, 0, -1, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 1 3, .triangle 0 2, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint b64406858d71ada7b5e9436abf71da7ebf5c10984305dae1345f8eb010f05899.
def localCycle00170 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 2]
    constant := ![-1, 4, -1, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 2 0, .triangle 4 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint b65b29d22ab43b6cc4474238ce9fbd11bd0cc815820bf6e6f1649f61de85b8ea.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint b6b5d76555c5141e928a2c48cbeb6658af7858e03f0934c3285eb024780dcb87.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint b751616cc7d58cf3b21b6010a8947a48390b01f038b62ac3067b8e55059f5851.
def localCycle00173 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 2, .triangle 23 1, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Cycle fingerprint b76f5970a5e7e0095222ce1816bfaa2ab82658f3249589feab8013c5aa092000.
def localCycle00174 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, 0, 0, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, true, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .triangle 20 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint b79e709aebe4637a627c2eb18d09717af89b85aabbf65fc6aa51ae17cd6deff6.
def localCycle00175 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .gapLower 1 4, .gapLower 1 3, .triangle 22 1, .corridorLower 4 5]

-- Cycle fingerprint b9dfce9293a9d388e8368c4220e6e02045d4ac2a3f433f817db0a207e32aa43f.
def localCycle00176 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 2]
    constant := ![4, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 0 2, .triangle 5 0, .triangle 15 0, .gapLower 2 0]

-- Cycle fingerprint b9fcd7856be30af5bf2db02fb8e635a27b99c1b91dca5e426c1466599d5c9408.
def localCycle00177 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint bafe9abc36a22a5b109c61084b68172d1e949f985247bd2f510d5b421dc9bd93.
def localCycle00178 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 33 1, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint bb6c37a8bc1ad4b254aa26695604817712ad28c50e63ea3e33a8cc17d47bd967.
def localCycle00179 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint bb7f0724a820593bf78a92694014a506fe18aae2ae4a1cfc45a56d7f7239c516.
def localCycle00180 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint bbce94a062a94f0a1d62e8fb1407577ca33c2d137088eb4fdc2f7a7f31186ed8.
def localCycle00181 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 1 5, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 1 3, .corridorLower 1 5]

-- Cycle fingerprint bda425742f4974cc56b9e254400177b0a5edac0f8593f4b6d959d7c4942891b5.
def localCycle00182 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, 0, -1, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 0, .gapLower 0 3, .triangle 8 0, .triangle 27 1, .triangle 15 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint be4ecf00c3e43a99195a857857f9e5e6b1741bc3402c72bd609a64ebeca69488.
def localCycle00183 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, -1, 0, -3, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint c1a6c560baf98a13faf9a3136cd44b848bdce5867c67ac5ce1da63da78d813d6.
def localCycle00184 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint c248298430e2a557bf65a7bb1565eba6973a7ace2d5c32b2a51d8c9439b533b0.
def localCycle00185 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![4, -2, 0, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 17 2, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint c34c491f67cb7076a8144930b9850a2e73253026bdd2c189adbbe9a797af61e1.
def localCycle00186 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 7 1, .triangle 5 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint c3a8353030d4fdbd4e39d85629843a7f81f99cdda3fbb0b7a48dc9d06178eb5d.
def localCycle00187 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![0, -1, -1, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint c55cdfe2403613308600deaf75f6517b3e5e972797fb4f295adc5be4ea85375f.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint c60356f64137be069534c61a41ba7e965a89edf949a744dcbbb76f12279c4354.
def localCycle00189 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, 0, -1, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 26 1, .triangle 15 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint c6b6fc39e56060dedb107dac7747afeb54ab2ad59c829ffcdadc34f979941226.
def localCycle00190 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 5 0, .triangle 27 0, .triangle 33 1, .gapUpper 5 3, .triangle 7 1]

-- Cycle fingerprint c8bab853be5104831a6ba0af2beb4ca38d3adbf9ae361e4742480169311cce0d.
def localCycle00191 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 6]
    constant := ![0, -1, -1, -1, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 8 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 3 0, .triangle 4 2]

-- Cycle fingerprint c8ff02093234d8a4664ba0dceb2eb7997a2e05d0d4cf6c73da535468db64e1fc.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ca0ec664ea6c7c7a2f9d11bd6fb968ce2512721b6d44cdb680966d50bdf6931d.
def localCycle00193 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, 0, -2, -1, 0, 0, -1, -1, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 4 0, .gapLower 0 2, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint cb132edf7c2edffc4781fab2d20c7ac895a386d60fd822fe41dcab8ade790784.
def localCycle00194 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .theta 1, .distance 1 4]
    constant := ![-2, 0, -1, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 0 2, .triangle 8 0, .triangle 18 2, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6]

-- Cycle fingerprint cb7617d85e6326bc3fb4ef715622994f08e49fdaaa77ea5a5d809faf11296d54.
def localCycle00195 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 20 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint ce592e8abc0e286214b38837b31230d157de726a722693f73cb8f044f1b32c79.
def localCycle00196 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint cf841b0d181253bc3b9cd843c24f3939aab5252c6ca8ba45dbcea848b6b3aa26.
def localCycle00197 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d094080db3439729097656ac39290b1b00395b9992d5dd1c319879ba64f73086.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint d12737e9d60f94b2e0634229cd8ad4550c8dac5884dbb152963c7bf81267d4af.
def localCycle00199 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d134f21f58dfb6cbec01a7a6836c82418b535cbd78966c98cc020e319816178d.
def localCycle00200 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint d1fdc4289eef28fe723f0e18497e5f5534558d5bb5bc789859234cb2c4cbe533.
def localCycle00201 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d3b2e30e93af8d45bed6df11ab98e3d2a9c9cf8c4d75e8faa16253a3069d85b8.
def localCycle00202 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -1, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint d868d9383797dc8ef2547a461985aa28955ce6ce3724026f7ddc5190c51c17ee.
def localCycle00203 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 2, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint da1597dc61595c0dccf088c17d961c2abac47b7208a1624d545709d0c018cc7e.
def localCycle00204 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5]
    constant := ![0, -1, -1, 4, -3, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 26 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 8 1, .triangle 7 0]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00205 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dacbfeef0b69650bf760768b53824ca310f775112060b869a8d2b2c9ba239e0d.
def localCycle00206 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2]
    constant := ![-1, 0, -2, 0, -2, 0, 0, 3, 0, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, true, false, true, true] }
  origin := ![.triangle 7 0, .triangle 17 2, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .triangle 8 1]

-- Cycle fingerprint db3d2474b78a7fa9addc5f899b9f05e673deb5b86ed34febbc6f9c50008d63f5.
def localCycle00207 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint dbf8017609852c67cfb5667a32eaaff5c1ffa828df30aa4c7fc29d1dca623f06.
def localCycle00208 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dc68496056b7966e9d23a2012c90cfbd13efa080d128fa97f24881739028c4e9.
def localCycle00209 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint dcbccf0f95fde8a444f9abdfccf746d38696192c79bfd33604e347eed075fdfc.
def localCycle00210 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dd3ac302e38d76b77b9035cf6f9c79afae67c0628b4f3f36f436eb84e8e1db19.
def localCycle00211 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 6]
    constant := ![0, 0, -1, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true, true, false, false] }
  origin := ![.triangle 23 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint dd3f34834abece82e9b4f76cdd62800880a4daa0b272ab749e1e2318c72ad487.
def localCycle00212 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint de486a8f29af80c652504ef5999e51afd36e484b7115cf602f6d55b06b45d240.
def localCycle00213 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint de5756f347f9750f5dc3cd3d94afa86f525b08afa56def6b42fd0393203ed248.
def localCycle00214 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5]
    constant := ![0, -2, -2, -1, 4, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0, .triangle 4 2, .triangle 8 1, .triangle 7 0]

-- Cycle fingerprint e016aa29d6792b7f64fff199c4f92def2822a3f0ac152fc8c7fd583c4b199fc1.
def localCycle00215 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint e0f56c14a6dad46de34103bdc4b330a36cc8b168a72d679bb4f325b12cd146c4.
def localCycle00216 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 27 1, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint e112cabbf5d8be32d857786ef255ee6f76778c75554208447e4a395681634eb2.
def localCycle00217 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 24 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint e184eaf5ccc930e1f915f6f62e9e0bf3140d0d1808657e4c8577ad386adcb872.
def localCycle00218 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 4 0, .gapLower 0 3, .gapLower 2 3, .triangle 17 2, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Cycle fingerprint e25edf239eb51fc34e4ae6f0eabd9d097352256229899a02f614270261a96335.
def localCycle00219 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint e407e714e04e6c486b795af1551458044f23e88655eabad571d7b5e62ebc7ba3.
def localCycle00220 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![0, -1, 0, 0, -1, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, true, false, false] }
  origin := ![.triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 23 1, .corridorLower 4 6, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint e64487fbd8b9bc9075de250f3db120c9faa2a547f15a099b9d994f1e969ccf88.
def localCycle00221 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint e73933bb0abeacd4492830bb9dea9b6e5b5c8e2221d2f1f9efa106b92c9345af.
def localCycle00222 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 5, .triangle 0 2, .gapUpper 2 5, .gapLower 4 4]

-- Cycle fingerprint e9b042ae66c38ff888ba523dfd3ad4be6369149c5042980b6771fa4ee2d10ed3.
def localCycle00223 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 4 6, .distance 0 4, .distance 0 1]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, true] }
  origin := ![.gapLower 1 4, .triangle 23 1, .gapUpper 4 2, .triangle 2 1]

-- Cycle fingerprint ebf5e00322d67dc704e4e0fa834968b03eaa1e971c91eec10db94a43ddfe05b2.
def localCycle00224 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 33 1, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint edb0df9c9aaa9f65afcf8f6d3e80f5edfd3c66692d68d0f0e980233b41c91a30.
def localCycle00225 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .triangle 8 1, .triangle 5 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint eeaca6769ca4977c23c26e1a36c26903fedd10b8afd04d950cba170fe6b29186.
def localCycle00226 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![0, -1, -1, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .triangle 5 0, .triangle 15 0, .gapLower 1 0, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint eed99b84b7f9bea298e2cb740fb0f25ecc17bef393f2f0bcb4a65c481d483674.
def localCycle00227 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -1, -1, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint f00cad1f9bf44eb0fe2372e224fdcc2e6e11db754e6dadd0e7ddafd7cd1f4f07.
def localCycle00228 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Cycle fingerprint f0a9a4ade1cad4e32e91df8d0671633ad3ea60fb0038429c005bc92516e8bc99.
def localCycle00229 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint f2833fde609529d33025e1ae065d6a7bf2c32e00394e810a4123e9e606674a78.
def localCycle00230 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5]
    constant := ![-2, -1, 4, 0, -2, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 23 2, .gapLower 1 4, .triangle 0 2, .triangle 7 0, .triangle 17 2]

-- Cycle fingerprint f2a5b046888f69a886a889932ef6837ce3dcd8bb83a9b49aa127ffe5c20dc65e.
def localCycle00231 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 2]
    constant := ![4, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 28 2, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 5 0, .triangle 15 0, .gapLower 2 0]

-- Cycle fingerprint f862b1d210faed7f302b620cf09910a7b3bb5ae245c5d01eeb3b200f3fc9280a.
def localCycle00232 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint f95ac124c7a46b4d1cf687087ae33527733326396814ebdf25e8ebbbf091352f.
def localCycle00233 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 1 3, .corridorLower 1 6]

-- Cycle fingerprint f9b435dbc854fab5e3616a7ef69880eb7f5a8e7b7329e85e0140c7d92b8c2f11.
def localCycle00234 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![-1, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 2 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint fbabc7c3afee4b3b8ebe73d7a21a9ce47c1f1d007a7ac13577b938f214ed06aa.
def localCycle00235 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint fc292621f8aea9717e6d5038b0de1d5d72eaee8d51689ba3595a2ed60fb510d4.
def localCycle00236 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint fc81817b37ab1ff310868912dd1214e511719270222f2c2699624a91409bc3a0.
def localCycle00237 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint fd9f249f7f6bdac201f804ae5cf72c2f02c5a22e809ba5af8a309cc3ad93aed2.
def localCycle00238 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint fdcc9c84ddb05f1be45672dba6d809ad3298d0bb2f44cf7b0e236bf4e21310ae.
def localCycle00239 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

def library : Library := fun id => if id < 120 then (if id < 60 then (if id < 30 then (if id < 15 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 11 then (if id < 9 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none)) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))) else (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))))) else (if id < 22 then (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 20 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)))) else (if id < 26 then (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))) else (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)))))) else (if id < 45 then (if id < 37 then (if id < 33 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))) else (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)))) else (if id < 41 then (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))))) else (if id < 52 then (if id < 48 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))) else (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)))) else (if id < 56 then (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))) else (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))))))) else (if id < 90 then (if id < 75 then (if id < 67 then (if id < 63 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))) else (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))) else (if id < 71 then (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))))) else (if id < 82 then (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)))) else (if id < 86 then (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))))) else (if id < 105 then (if id < 97 then (if id < 93 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))) else (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))) else (if id < 101 then (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))))) else (if id < 112 then (if id < 108 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))) else (if id < 116 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)))))))) else (if id < 180 then (if id < 150 then (if id < 135 then (if id < 127 then (if id < 123 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))) else (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)))) else (if id < 131 then (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))) else (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))))) else (if id < 142 then (if id < 138 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))) else (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)))) else (if id < 146 then (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))) else (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)))))) else (if id < 165 then (if id < 157 then (if id < 153 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none))) else (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none)))) else (if id < 161 then (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))))) else (if id < 172 then (if id < 168 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))) else (if id < 170 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)))) else (if id < 176 then (if id < 174 then (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none))) else (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))))))) else (if id < 210 then (if id < 195 then (if id < 187 then (if id < 183 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none))) else (if id < 185 then (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)))) else (if id < 191 then (if id < 189 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))) else (if id < 193 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none))))) else (if id < 202 then (if id < 198 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none))) else (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)))) else (if id < 206 then (if id < 204 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none))) else (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none)))))) else (if id < 225 then (if id < 217 then (if id < 213 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none))) else (if id < 215 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none)))) else (if id < 221 then (if id < 219 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none))) else (if id < 223 then (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none))))) else (if id < 232 then (if id < 228 then (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none))) else (if id < 230 then (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none)) else (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none)))) else (if id < 236 then (if id < 234 then (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none)) else (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none))) else (if id < 238 then (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none)) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![3, 2, 1, 5, 4, 6], ![2, 3, 0, 5, 4, 6], ![1, 3, 0, 5, 4, 6], ![1, 2, 0, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 1, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 67 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15616)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![3, 2, 1, 5, 4, 6], ![2, 3, 0, 5, 4, 6], ![1, 3, 0, 5, 4, 6], ![1, 2, 0, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 165 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15617)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![3, 2, 1, 5, 4, 6], ![2, 3, 0, 5, 4, 6], ![1, 3, 0, 5, 4, 6], ![1, 2, 0, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 177 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15618)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![3, 2, 1, 5, 4, 6], ![2, 3, 0, 5, 4, 6], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 32 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15619)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![3, 2, 1, 5, 4, 6], ![2, 3, 0, 5, 4, 6], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 209 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15620)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![3, 2, 1, 5, 4, 6], ![2, 3, 0, 5, 4, 6], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 176 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15621)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![3, 2, 1, 5, 4, 6], ![2, 3, 0, 5, 6, 4], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 2, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 82 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15622)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![3, 2, 1, 5, 4, 6], ![2, 3, 0, 5, 6, 4], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 2, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 162 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15623)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![3, 2, 1, 5, 4, 6], ![2, 3, 0, 5, 6, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![0, 4, 1, 5, 2, 3]], proof := .tail 231 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15624)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![3, 2, 1, 5, 4, 6], ![2, 3, 0, 6, 5, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 1, 2, 3]], proof := .tail 46 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15625)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![3, 2, 1, 5, 6, 4], ![2, 3, 0, 5, 6, 4], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 28 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15626)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![3, 2, 1, 5, 6, 4], ![2, 3, 0, 5, 6, 4], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 41 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15627)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![3, 2, 1, 5, 6, 4], ![2, 3, 0, 5, 6, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![4, 0, 1, 5, 2, 3]], proof := .tail 231 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15628)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![3, 2, 1, 5, 6, 4], ![2, 3, 0, 6, 5, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 1, 2, 3]], proof := .tail 52 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15629)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![3, 2, 1, 6, 5, 4], ![2, 3, 0, 6, 5, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 1, 2, 3]], proof := .low (![239, 157, 1, 159, 97, 48, 187, 29, 86, 86, 124, 93, 226, 234, 75, 95, 93, 167, 169, 193, 117, 87, 39, 79, 164, 147, 102, 58]) }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15630)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![3, 2, 1, 6, 5, 4], ![2, 3, 0, 6, 5, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 1, 2, 3]], proof := .low (![239, 157, 1, 159, 97, 126, 187, 29, 86, 86, 124, 31, 226, 234, 75, 95, 142, 167, 169, 193, 117, 87, 39, 79, 164, 147, 102, 58]) }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15631)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![3, 2, 6, 1, 5, 4], ![2, 3, 6, 0, 5, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 1, 0, 2, 3]], proof := .tail 149 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15632)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![3, 6, 2, 1, 5, 4], ![2, 3, 6, 0, 5, 4], ![1, 3, 6, 0, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 1, 2, 0, 3]], proof := .tail 198 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15633)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![2, 3, 6, 0, 5, 4], ![1, 3, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 1, 2, 3, 0]], proof := .tail 203 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15634)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![2, 3, 6, 0, 5, 4], ![1, 6, 3, 0, 5, 4], ![1, 6, 2, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 1, 3, 2, 0]], proof := .tail 156 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15635)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![2, 6, 3, 0, 5, 4], ![1, 6, 3, 0, 5, 4], ![6, 1, 2, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 3, 1, 2, 0]], proof := .tail 98 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15636)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![6, 2, 3, 0, 5, 4], ![6, 1, 3, 0, 5, 4], ![6, 1, 2, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 44 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15637)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![3, 2, 6, 1, 5, 4], ![2, 3, 6, 0, 5, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .low (![139, 157, 59, 108, 99, 90, 60, 107, 225, 225, 33, 112, 10, 170, 25, 47, 81, 54, 146, 153, 88, 45, 211, 7, 24, 161, 3, 191]) }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15638)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![3, 6, 2, 1, 5, 4], ![2, 3, 6, 0, 5, 4], ![1, 3, 6, 0, 5, 4], ![1, 2, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 1, 2, 0, 3]], proof := .low (![116, 157, 38, 108, 118, 90, 62, 152, 84, 171, 202, 182, 138, 236, 25, 0, 81, 54, 146, 5, 88, 45, 211, 7, 233, 220, 6, 21]) }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15639)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![2, 3, 6, 0, 5, 4], ![1, 3, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 196 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15640)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![2, 3, 6, 0, 5, 4], ![1, 6, 3, 0, 5, 4], ![1, 6, 2, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 1, 3, 2, 0]], proof := .tail 106 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15641)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![2, 6, 3, 0, 5, 4], ![1, 6, 3, 0, 5, 4], ![6, 1, 2, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 3, 1, 2, 0]], proof := .tail 2 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15642)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![6, 2, 3, 0, 5, 4], ![6, 1, 3, 0, 5, 4], ![6, 1, 2, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 160 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15643)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 0, 5, 4, 6], ![1, 2, 0, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 1, 0, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 22 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15644)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 0, 5, 4, 6], ![1, 2, 0, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 1, 0, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 104 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15645)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 1, 0, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 155 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15646)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![2, 3, 5, 0, 6, 4], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 1, 0, 2, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 215 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15647)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![3, 2, 5, 1, 6, 4], ![2, 3, 5, 0, 6, 4], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 0, 2, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 215 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15648)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 0, 5, 4, 6], ![1, 2, 0, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 1, 0, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 77 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15649)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 1, 0, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 77 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15650)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![2, 3, 5, 0, 6, 4], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 1, 0, 2, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 173 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15651)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![3, 2, 5, 1, 6, 4], ![2, 3, 5, 0, 6, 4], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 0, 2, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 92 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15652)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 1, 0, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 228 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15653)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![2, 3, 5, 0, 6, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 1, 0, 6, 2, 3], ![0, 4, 1, 5, 2, 3]], proof := .tail 103 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15654)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![3, 2, 5, 1, 6, 4], ![2, 3, 5, 0, 6, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 0, 6, 2, 3], ![4, 0, 1, 5, 2, 3]], proof := .tail 96 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15655)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![3, 2, 5, 6, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 0, 2, 3, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 215 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15656)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![3, 2, 5, 6, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 0, 2, 6, 3], ![4, 1, 0, 2, 5, 3]], proof := .tail 92 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15657)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![3, 2, 5, 6, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 0, 6, 2, 3], ![4, 1, 0, 5, 2, 3]], proof := .tail 94 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15658)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![3, 2, 6, 5, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 0, 2, 3]], proof := .tail 143 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15659)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![3, 2, 6, 5, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 0, 2, 3]], proof := .tail 4 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15660)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![3, 6, 2, 5, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 6, 0, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 2, 0, 3]], proof := .tail 43 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15661)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![3, 6, 2, 5, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 3, 6, 0, 5, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 2, 0, 3]], proof := .tail 4 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15662)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 2, 3, 0]], proof := .tail 63 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15663)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 6, 3, 0, 5, 4], ![1, 6, 2, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 3, 2, 0]], proof := .tail 190 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15664)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 3, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 2, 3, 0]], proof := .tail 4 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15665)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 6, 3, 0, 5, 4], ![1, 6, 2, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 3, 2, 0]], proof := .tail 4 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15666)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![2, 6, 3, 5, 0, 4], ![1, 6, 3, 0, 5, 4], ![6, 1, 2, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 3, 1, 2, 0]], proof := .tail 8 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15667)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![6, 2, 3, 5, 0, 4], ![6, 1, 3, 0, 5, 4], ![6, 1, 2, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 137 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15668)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 2, 6, 5, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 163 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15669)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 6, 2, 5, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 3, 6, 0, 5, 4], ![1, 2, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 163 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15670)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 3, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 89 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15671)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 6, 3, 0, 5, 4], ![1, 6, 2, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 3, 2, 0]], proof := .tail 186 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15672)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![2, 6, 3, 5, 0, 4], ![1, 6, 3, 0, 5, 4], ![6, 1, 2, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 3, 1, 2, 0]], proof := .tail 27 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15673)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![6, 2, 3, 5, 0, 4], ![6, 1, 3, 0, 5, 4], ![6, 1, 2, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 68 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15674)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 5, 0, 4, 6], ![1, 2, 0, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 1, 2, 0, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 74 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15675)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 5, 0, 4, 6], ![1, 2, 0, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 1, 2, 0, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 35 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15676)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 5, 0, 6, 4], ![1, 2, 0, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 1, 2, 0, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 155 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15677)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![2, 3, 5, 0, 6, 4], ![1, 3, 5, 0, 6, 4], ![1, 2, 0, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 1, 2, 0, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 199 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15678)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![3, 5, 2, 1, 6, 4], ![2, 3, 5, 0, 6, 4], ![1, 3, 5, 0, 6, 4], ![1, 2, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 0, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .low (![61, 157, 183, 109, 15, 11, 30, 195, 180, 36, 141, 26, 17, 13, 229, 70, 115, 179, 66, 230, 218, 123, 76, 200, 181, 34, 128, 83]) }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15679)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 5, 0, 4, 6], ![1, 2, 0, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 1, 2, 0, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 212 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15680)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 5, 0, 6, 4], ![1, 2, 0, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 1, 2, 0, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 77 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15681)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![2, 3, 5, 0, 6, 4], ![1, 3, 5, 0, 6, 4], ![1, 2, 0, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 1, 2, 0, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 113 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15682)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![3, 5, 2, 1, 6, 4], ![2, 3, 5, 0, 6, 4], ![1, 3, 5, 0, 6, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 0, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 132 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15683)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![3, 5, 2, 6, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 5, 0, 6, 4], ![1, 2, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 0, 3, 6], ![4, 1, 0, 2, 3, 5]], proof := .low (![135, 157, 100, 122, 223, 204, 80, 18, 206, 56, 56, 189, 121, 214, 72, 85, 185, 158, 37, 145, 20, 217, 175, 49, 73, 151, 110, 64]) }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15684)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![3, 5, 2, 6, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 5, 0, 6, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 0, 6, 3], ![4, 1, 0, 2, 5, 3]], proof := .tail 55 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15685)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![3, 5, 6, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 5, 6, 0, 4], ![1, 2, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 0, 3, 6], ![4, 1, 2, 0, 3, 5]], proof := .low (![120, 157, 12, 140, 223, 222, 42, 174, 23, 166, 166, 134, 14, 114, 111, 85, 168, 158, 150, 145, 136, 217, 175, 194, 73, 151, 110, 91]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15686)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![3, 5, 6, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 5, 6, 0, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 0, 6, 3], ![4, 1, 2, 0, 5, 3]], proof := .low (![120, 157, 12, 140, 223, 222, 42, 174, 23, 166, 166, 134, 14, 114, 111, 85, 168, 158, 150, 145, 136, 217, 175, 194, 73, 151, 110, 91]) }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15687)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 5, 6, 0, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 6, 0, 3], ![4, 1, 2, 5, 0, 3]], proof := .tail 105 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15688)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 6, 5, 0, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 2, 0, 3]], proof := .tail 210 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15689)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 3, 6, 5, 0, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 2, 0, 3]], proof := .tail 172 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15690)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 5, 6, 0, 4], ![1, 2, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 6, 0, 3], ![4, 1, 2, 5, 3, 0]], proof := .tail 208 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15691)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 2, 3, 0]], proof := .tail 210 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15692)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 3, 2, 0]], proof := .tail 119 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15693)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 2, 3, 0]], proof := .tail 172 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15694)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 3, 2, 0]], proof := .tail 119 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15695)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![2, 6, 3, 5, 0, 4], ![1, 6, 3, 5, 0, 4], ![6, 1, 2, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 3, 1, 2, 0]], proof := .tail 144 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15696)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![6, 2, 3, 5, 0, 4], ![6, 1, 3, 5, 0, 4], ![6, 1, 2, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 219 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15697)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 3, 6, 5, 0, 4], ![1, 2, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 101 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15698)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 89 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15699)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 3, 2, 0]], proof := .tail 130 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15700)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![2, 6, 3, 5, 0, 4], ![1, 6, 3, 5, 0, 4], ![6, 1, 2, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 3, 1, 2, 0]], proof := .tail 131 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15701)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![6, 2, 3, 5, 0, 4], ![6, 1, 3, 5, 0, 4], ![6, 1, 2, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 207 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15702)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 5, 0, 4, 6], ![1, 2, 5, 0, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 1, 2, 3, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 57 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15703)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 5, 0, 4, 6], ![1, 2, 5, 0, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 1, 2, 3, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 221 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15704)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 3, 5, 0, 6, 4], ![1, 2, 5, 0, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 1, 2, 3, 0, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 53 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15705)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![2, 3, 5, 0, 6, 4], ![1, 3, 5, 0, 6, 4], ![1, 2, 5, 0, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 1, 2, 3, 0, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 40 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15706)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![5, 3, 2, 1, 6, 4], ![2, 3, 5, 0, 6, 4], ![1, 3, 5, 0, 6, 4], ![1, 2, 5, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 51 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15707)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![5, 3, 2, 6, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 5, 0, 6, 4], ![1, 2, 5, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 201 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15708)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![5, 3, 6, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 5, 6, 0, 4], ![1, 2, 5, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 201 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15709)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![5, 6, 3, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 178 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15710)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 3, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 197 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15711)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 5, 6, 0, 4], ![1, 2, 6, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 6, 3, 0], ![4, 1, 2, 5, 3, 0]], proof := .tail 205 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15712)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 2, 3, 0], ![4, 1, 5, 2, 3, 0]], proof := .tail 69 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15713)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 2, 3, 0], ![4, 1, 5, 3, 2, 0]], proof := .tail 188 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15714)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 1, 2, 3, 0]], proof := .tail 238 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15715)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 1, 3, 2, 0]], proof := .tail 188 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15716)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 6, 3, 5, 0, 4], ![1, 6, 3, 5, 0, 4], ![6, 1, 2, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 232 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15717)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 2, 3, 5, 0, 4], ![6, 1, 3, 5, 0, 4], ![6, 1, 2, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 129 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15718)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 192 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15719)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 5, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 78 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15720)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 6, 3, 5, 0, 4], ![1, 6, 3, 5, 0, 4], ![6, 1, 2, 5, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 237 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15721)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 2, 3, 5, 0, 4], ![6, 1, 3, 5, 0, 4], ![6, 1, 2, 5, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 184 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15722)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 5, 3, 0, 4, 6], ![1, 5, 2, 0, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 1, 3, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 154 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15723)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 5, 3, 0, 4, 6], ![1, 5, 2, 0, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 1, 3, 2, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 148 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15724)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![2, 3, 5, 0, 4, 6], ![1, 5, 3, 0, 6, 4], ![1, 5, 2, 0, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 1, 3, 2, 0, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 213 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15725)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![2, 3, 5, 0, 6, 4], ![1, 5, 3, 0, 6, 4], ![1, 5, 2, 0, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 1, 3, 2, 0, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 71 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15726)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![5, 3, 2, 1, 6, 4], ![2, 3, 5, 0, 6, 4], ![1, 5, 3, 0, 6, 4], ![1, 5, 2, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 3, 2, 0, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 227 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15727)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![5, 3, 2, 6, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 5, 3, 0, 6, 4], ![1, 5, 2, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 3, 2, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 19 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15728)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![5, 3, 6, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 5, 3, 6, 0, 4], ![1, 5, 2, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 3, 2, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 216 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15729)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![5, 6, 3, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 5, 3, 6, 0, 4], ![1, 5, 2, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 3, 2, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 65 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15730)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![5, 6, 3, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 5, 6, 3, 0, 4], ![1, 5, 6, 2, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 3, 2, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 224 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15731)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 5, 3, 6, 0, 4], ![1, 5, 2, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 3, 2, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 125 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15732)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 5, 6, 3, 0, 4], ![1, 5, 6, 2, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 143 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15733)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 6, 5, 3, 0, 4], ![1, 5, 6, 2, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 3, 6, 2, 0], ![4, 1, 3, 5, 2, 0]], proof := .tail 210 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15734)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 5, 6, 0, 4], ![1, 6, 5, 3, 0, 4], ![1, 6, 5, 2, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 3, 2, 0], ![4, 1, 5, 3, 2, 0]], proof := .tail 235 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15735)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 6, 5, 3, 0, 4], ![1, 6, 5, 2, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 3, 2, 0], ![4, 5, 1, 3, 2, 0]], proof := .tail 235 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15736)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 6, 3, 5, 0, 4], ![1, 6, 5, 3, 0, 4], ![6, 1, 5, 2, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 50 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15737)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 2, 3, 5, 0, 4], ![6, 1, 5, 3, 0, 4], ![6, 1, 5, 2, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 219 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15738)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 3, 6, 5, 0, 4], ![1, 6, 5, 3, 0, 4], ![1, 6, 5, 2, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 133 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15739)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![2, 6, 3, 5, 0, 4], ![1, 6, 5, 3, 0, 4], ![6, 1, 5, 2, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 127 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15740)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 2, 3, 5, 0, 4], ![6, 1, 5, 3, 0, 4], ![6, 1, 5, 2, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 207 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15741)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![2, 5, 3, 0, 4, 6], ![1, 5, 3, 0, 4, 6], ![5, 1, 2, 0, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 9 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15742)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![2, 5, 3, 0, 4, 6], ![1, 5, 3, 0, 4, 6], ![5, 1, 2, 0, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 16 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15743)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (15616 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 15616 ≤ id.val) (hhigh : id.val < 15744) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 15616)) = true := by
  let j : Fin 128 := ⟨id.val - 15616, by omega⟩
  have hsum : 15616 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (15616 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard122
