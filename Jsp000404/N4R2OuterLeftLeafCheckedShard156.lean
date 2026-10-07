import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard156
open N4R2OuterLeftReplay

-- Cycle fingerprint 01a3d2c0e6849771ce3248dc00788564d8faaba1ea61762d2ac44aa3cfb30edf.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 2, .distance 1 4, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 15 1, .triangle 16 2, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 01b5887ca94e8ea5cf76be12585e985677fcf7549ad466b2b01f2bbe66f9e7e7.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 2]
    constant := ![-2, -2, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 21 2, .gapLower 1 2]

-- Cycle fingerprint 08265ebd66184fc37e70df1d628631315bac1d88bf9a1ad42e669216471f7396.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 2, .distance 1 4, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 15 1, .gapLower 1 1, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 0831b7d600aa086e21a6586bb1fb14bead9b78e778e47b4168ab7c781d231c73.
def localCycle00003 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, 0, -1, 0, -1, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 26 0, .triangle 10 0, .gapLower 0 3, .triangle 6 2, .triangle 13 0, .triangle 32 2, .triangle 21 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 09d532b8138b6cfda410e808acdb577ae6a7c435b00724e922ccc7dba7fccac3.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .gapLower 1 4, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 0bba5f617997fee0e4ba6f77d0187777784a478696563b47f717aac83f405858.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 20 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 0bee15affba941d3c6481f9e5a6c3ec7fec576fcb1bf11e9fc12073146b7d19c.
def localCycle00006 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 0cf79cead8aa09973f711c6b739b71200a63074ca285eed03ef832c4a5d0f092.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4]
    constant := ![-1, 0, 0, 2, -3, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorLower 3 4, .thetaLower 3, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 15 1, .triangle 16 0, .triangle 25 1]

-- Cycle fingerprint 0cff143aba2cd8ca4f55a9f4297342ed96825bb46ea205d4b6fa2b8c6a0ade7c.
def localCycle00008 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![-1, 0, -1, 0, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true, false, true, true, false, true] }
  origin := ![.triangle 11 0, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .triangle 1 2]

-- Cycle fingerprint 0f61185c1456498e928c099bd7bcc9b93dc731d31d4680e9641af90230c50e95.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 3 6]
    constant := ![-1, 3, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorLower 3 6, .corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 20 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .triangle 32 2]

-- Cycle fingerprint 0fd60db1a9842a61b30fba5d55b4e35f313098d4ac027271e51ad09685fcf340.
def localCycle00010 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 1253e3375c82ba843f28ba082779f0efd5fc5b18d7fbdcc1e53a8abb5f213fcf.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![0, -2, -1, 0, -1, 0, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, true, true, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint 12e21d60bbc1e152fedbb58304ea33c91d2d1b70e7c6ce8acfff93cedfda13a6.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![0, 2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.triangle 6 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 5 1]

-- Cycle fingerprint 14cd27a65f912a5687e07a39bffbf4ddb8aa1d235d2cd350e1196ce36d8090af.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 4, .distance 3 4]
    constant := ![-1, 0, 0, 3, -3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 18 1, .triangle 16 0, .triangle 25 1]

-- Cycle fingerprint 183fb7a0efa3b66b3e2c4c285ae2f6e587b5f298beb04572583e46c965bb4546.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 33 2, .gapLower 3 0]

-- Cycle fingerprint 19b5b3615482ca34c583f42b6ec81b47f09eb984cd2b8559125953a11624719c.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 21 1, .triangle 20 2, .gapLower 1 2, .triangle 16 2, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 1a3a309338ceecc01f922f0da68fc446e9c6b7b3266942cba2ee2e6c3c0afd97.
def localCycle00016 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 1abba9554403534f8924d51c559c341aa3e5131d6b453d82674218b4fd1bc6d1.
def localCycle00017 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 6, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 1ba8a359a4d61d031c6360457c499bf1bf060104071d15bdef08a67f223f3d88.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 1d617e1ea356bf82a15c5d297c933386f325afd59974fbcbe424513c3f98c3f2.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 1e3723f760054f2d3c262c1b64dcd4050bbdda816f1cee90d6f5bf134d25617c.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 202e90d1c67b5917d008f0836b8d96f7d280ac3dd10fecfc424df7ff163d76e3.
def localCycle00021 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![0, 0, -2, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 21 2, .triangle 23 1, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 2032958ffe9ebd091e893c5c320685955b94cbfdabddc087face4fd0327e971c.
def localCycle00022 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![0, -1, -1, -1, 0, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, true, false, true, true, false, true] }
  origin := ![.triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .triangle 1 2]

-- Cycle fingerprint 2100e727abcf67e14c197ad76a7080d947dca4df856ffb91e1e496767bf8d6ae.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![-1, -1, -1, -1, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 21 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 21247e313a3ea778dc8831d383fdde0957df5140463b38d2633222ffc9794929.
def localCycle00024 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 1 4]
    constant := ![-3, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 21 1, .triangle 15 1, .triangle 16 2]

-- Cycle fingerprint 220ffb3b0b5eefab76c7af18605f8f85ed0532b0905d0487cfeb777032e405ee.
def localCycle00025 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 21 1, .triangle 15 1, .gapLower 1 1, .corridorLower 1 4, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 2585c1c8ea923e46653af965712e979aa1bee543afb98cc027e19027742249c0.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![0, -2, -1, 0, -1, 0, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, true, true, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 26dfd7c651c61eb857507250e0daec6c3c037e5347ebb7a27b6db6765d9e9de9.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 29ac4c354ae2d31c1a1bddd550803e6ca81a00495bd77049aac89715f063028d.
def localCycle00028 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 3 5, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 26 1, .triangle 10 0, .triangle 1 1, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 2ad2745ed128b39c4d86c723cf1e017332832945fc19941969f4dda900daf42e.
def localCycle00029 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .gapLower 1 3, .triangle 23 1]

-- Cycle fingerprint 2c588bd75aa45b73515e05ad9762e7f830f103452dbb71fa0bd475e6ee3ef101.
def localCycle00030 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 2cd2c707e1d607393d2f38878bc1015c0d2c5d0a4a63e361f0e29f66dcf26fd7.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1]
    constant := ![2, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 4]

-- Cycle fingerprint 2f744e89db2db3755747ba8006683e46896f0c29c93fa4e546d2d4ac7a97cc1e.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 3 4]
    constant := ![-1, 0, 0, 3, -3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1, .triangle 21 0, .triangle 32 1]

-- Cycle fingerprint 3272e9b8b1b22678b72b3f72de6e4a3e203044779bd79254947787f88dd6ce34.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 0, .triangle 1 1, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 3338ae35ccff9f2b60612bc4ba35a882349f8c11c87914f3734123c90e148f96.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 15 1, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 338d8afce3abf62b00e9ace3c97da1946554e66fd622e6dd307f4715ffb1ff47.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![0, -1, -1, 0, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, true, true, false, true] }
  origin := ![.triangle 10 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .triangle 1 2]

-- Cycle fingerprint 362f3c44205a3a87f7351377798da7512ca711185b7c794ebf44a94720aebd07.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 2]
    constant := ![-2, -2, 0, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 21 1, .triangle 15 1]

-- Cycle fingerprint 370bdeb46b319fa632902e917326466afcc86370a6b479df9b9ddaf72825e3d7.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 3c6dff3232f31933db65af9491aa6649965c5933a937cfd36a4fc7783ad79025.
def localCycle00038 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 6 2, .gapUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0]

-- Cycle fingerprint 3c97c9069fa7ea5b598d9fbf53e7e0d22da9fb3805902e8d2382d5b18a668d69.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 3fb39e664c4bcc4d1b98f059f2aed669991aa3b446ca2cd0267bf9abebd31b9d.
def localCycle00040 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .corridorLower 1 2]

-- Cycle fingerprint 41414140b04ce34b94b12752aee8a9214438bc9a3bad00ced23b78aa6de67d28.
def localCycle00041 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint 43f1bfc35b49ab4b6b72b0d96b511e7390e259a50edb11228931cd82aec47ae3.
def localCycle00042 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, -2, -1, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 4, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint 44bcdc306fb21d2c2ed7341690d3680b348e8f877ea80ab621568dc715b96381.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 45e46d479d79784485c4ecd9bad5cd0b68a1f0387e8d2900272e981e4d827bd7.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 4, .corridorUpper 0 1]

-- Cycle fingerprint 47eddf3839efde1b1b926343ca63a4c812c95eb6882951c52e5c082eb0d0bfe5.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 493adca3f686d53c3fb2a9116acda07b196b8a0c7afccad937bb7cb394e94b8c.
def localCycle00046 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3]
    constant := ![0, -2, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 17 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 4a16a0b36bdf0415a0c36f028506114c8de4c7e4ff24753426764fd4647c15b6.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -1, 0, 1, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 16 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 1 0, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint 4f944103062d08b28d43da6c7019abfeb92c8019cb1aa0ca546fb5dcc8936b9a.
def localCycle00048 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 3]

-- Cycle fingerprint 51a6d8af245decf7a36617585fef1d66c6590511624b6432a3789d488fe81e27.
def localCycle00049 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint 62115da7ab6abcc9b0c868d0c279428a4eed47d307cc0b926065a67199377eab.
def localCycle00050 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint 63a7bcb796605a5ee88703f39a34e022c0dd34430d322b68b66789e800528101.
def localCycle00051 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 2]

-- Cycle fingerprint 64a5afaae55fa81d7e7510ad41226d257db83c340dad71ecf011c405682ec436.
def localCycle00052 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 4, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 1, .gapLower 1 1, .triangle 16 1]

-- Cycle fingerprint 67d0aa3c599eae7a286d69d8977737189bd9a96bc5c195f2ca2cf7a3b474daac.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![-2, -1, -1, 0, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 16 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 4 0, .triangle 21 1, .triangle 20 2]

-- Cycle fingerprint 6a899ce1b883eba9dec3ae8cf2de50034b20555e20051b4fb0449fcf8e1271d5.
def localCycle00054 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 4, .corridorUpper 0 1, .triangle 1 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 6ad0fdeb96793441b26a5a92cfd99f1cca078ae3283257d4fc9230f8531b9287.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero, .theta 6, .distance 1 6, .distance 1 3]
    constant := ![0, -3, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false, true, true] }
  origin := ![.triangle 20 2, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3, .thetaUpper 6, .gapUpper 6 0, .triangle 21 1]

-- Cycle fingerprint 6cdb5dfc195c5b6fede2d6cd80e55b4eb38f23662952c5a10493281cbc71c224.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 6e671a4e7a4bed133ef796ba2245dd0b857225e476b13eb087e5368de0328652.
def localCycle00057 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 4, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 23 0, .corridorLower 1 4]

-- Cycle fingerprint 6eea9c28796248681967b34bd2b4cad79dbf9c71db06e5e99389c683956db06c.
def localCycle00058 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 6, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 20 1, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 72fbeee891becab5bff3b18b7c6a9f1d5fe651826cb65b4c04797abb1f4381ab.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .gapLower 3 0]

-- Cycle fingerprint 736c960af437e07858e8a216a34d3caa11f3e36054489238fa1f18bddb642646.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 757d3e9b5bc75fe74ac4c759069c48265bf5f2f4d28fc8a205f937626087c27e.
def localCycle00061 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 76c7132ab27e50a5557dbe242682452dfbfd854a870e74c81fad56039980e1ff.
def localCycle00062 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 1 1, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 7882eb6eb9c8dd879dfa6d628247a155a3b8979a3ddffa01018aca7be8573719.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 78b57c22076a9792f22d4c1b2913d9990d6f2da34827fcc31aee5561050b5f32.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .corridorLower 3 5]

-- Cycle fingerprint 797952f2e9951441611524e69123a16b685e8e4b2bc30c034bf8cf92ccfde2f8.
def localCycle00065 : Cycle where
  length := 5
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 33 1, .gapUpper 5 1, .triangle 20 1, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint 7a8c471875415d19244a80a27cd856f734d1cc58fd2d98bd365cd3fbb8cdcba8.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 16 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 1 0, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint 7ae8bccb7c2ac2a0a76e3b48be9a02892aafaac2b0640034f913aafb9125dcda.
def localCycle00067 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 6 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 5 0]

-- Cycle fingerprint 7b67605c94c2724a675b36e79ccf102a58d5adea2da10e182a7141670aeaec1f.
def localCycle00068 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 1 1, .triangle 20 2, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 7c037f17be2f50b8aa8b1a2df1975ebdde14f5be23498f536338787c838f7574.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 10 0, .triangle 1 1, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 7c809b178a96e6558457d75a4e650a0bfedce7b0e5827433670f336db9d96a40.
def localCycle00070 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 802012efaaa9f46130b9e5c3d4fa00d9a396d329396b77fe09bd710028ba08fd.
def localCycle00071 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 21 1, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 83429d87c98ebcbead8544d88d5eea80caa85b0d48dc7d29467bd659b3ada5ed.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6]
    constant := ![-2, -2, -1, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 4, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 21 2]

-- Cycle fingerprint 854fbde85cab74443ac0be48e01796f455bfd95e0c9ff8306e4b36597ebf10bf.
def localCycle00073 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 33 1, .gapUpper 5 1]

-- Cycle fingerprint 87ca585f6f040fe532346deb65fb56fcabaa340fc5c65494fc179850f30f2c57.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 8826069bc41f788bffc10f25ee2bbac7a002fdf2028fea2fabf7d4885c64dbf8.
def localCycle00075 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 8bf9409874741cafefb654a843188ba6979d7f7840cb2438aec52fed392d007e.
def localCycle00076 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, 0, -1, 0, 0, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 8ed033d4abf38c744466f9d4c57f10c7a57d47a80b842fa6d752650a399770e7.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 90d28ad6a787faf1a01d049f69804d9af1ee05b30f0d4d4afbb4e5c57fff1a11.
def localCycle00078 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 92531c4850b49fd6ff94b9c9bad403a42252e6f7bfb2d35d13eba18d7ffebc0f.
def localCycle00079 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 927693ad492e9f32b4282c491b756dba56814eee3c3262006f1c35ab7eb476d2.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 2, .triangle 24 1, .triangle 17 1, .triangle 16 2, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 949358490ac038bb289b33817a68d559c7459ef9c9351d918e5540e60585036d.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4]
    constant := ![-3, 3, -1, 0, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .triangle 16 2]

-- Cycle fingerprint 95250169648e04356769dad9886c3c962493ccaff37763887fbf210eaff8ca53.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 21 1, .triangle 20 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 4, .thetaLower 1]

-- Cycle fingerprint 95ca0996a856361a50f7c22f9ec689034f11745692645cabe63a860b15ffe307.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, -1, 3, -1, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 16 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 30 1, .triangle 33 0, .triangle 20 0, .gapLower 1 2]

-- Cycle fingerprint 969118147c58e5257c0a79db26355ec4e775b2dc2405f3a5896f726d2f4c1a7b.
def localCycle00084 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 21 2, .gapLower 1 2, .corridorLower 1 2]

-- Cycle fingerprint 96a8b97b121f1d474d15793ea1aac8cabc3cb40aa0b37fabbcd8d879799bb2d1.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 96c8b5f387e06ff9e66c66a31f5fb70869193e6280547c08e96b0ac5cff4e158.
def localCycle00086 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, 0, -2, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 16 2, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint 97b9f3d79f6af87509bd8c1a74a0557cf671d46739e41d905c49d30a6e157d23.
def localCycle00087 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint 9a0b6a9c1fc285801e4a1711a2a5add35786043836cf63827e0926f1be769d17.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1]
    constant := ![1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 21 1, .triangle 15 1, .triangle 16 0, .corridorLower 2 4, .thetaNext 1]

-- Cycle fingerprint 9f16c253f991cc435a52bb9490137249c0b69a50ae618af3f1eabbb29618cabd.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint a0a18ea5bcb0c14f3a01cef019720fc6f04c64c88ef8803912045b7b4df97a22.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 30 1, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint a19b9cd2dea680ae86c233256e6c00ebebfd24fe64d7e088d409a333603bc37c.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .corridorLower 2 4, .thetaLower 2]

-- Cycle fingerprint a1a60cc9e92f2f4b5fb29f1b8259da1a8462bd04d16c95fb20a8be2cfd152418.
def localCycle00092 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 33 1, .gapUpper 5 1]

-- Cycle fingerprint a3c91c0e325f8febdfbbb7d7646add0d1cb963e4b99e81a0c4a0b440a3efc396.
def localCycle00093 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint a571fbfd696a1a17ee64c5acdd451bb6f40dfee7c0cd93f8e74dc24ec911ddd8.
def localCycle00094 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint a700ee72db308d6b659f6a1a00bc0a2628c0ea54c029fe4904e5a685b2e25dda.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 16 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint a723e10c9510156fdc18e63cb4abb50fdbe1d713fcd1bf2b4d9aaa4240dd369d.
def localCycle00096 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint a80cb93daf7c951d8942e61bef17f6102812d081e6eab0337c06465bd07b1484.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6]
    constant := ![-2, 0, -2, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 17 1, .gapLower 1 1, .corridorLower 1 4, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2]

-- Cycle fingerprint a8961bd15da6dc022ce1b916549f6cbcf7bb004fd23f1cd35c81b6985cc44563.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 0 3, .distance 3 5]
    constant := ![-1, 0, -1, -1, -1, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 5 2, .triangle 10 0]

-- Cycle fingerprint ac7c67054386444a09e3d283ec8ec1c503f408ca61a1dc4a09535002c239470e.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint aca5c3c2ef3c8569a65d820df9a1c42c20c361acbfc145e92a94e61e06e226c0.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint b051505a409051fdd24fc267b9883bf8d57e6f581442eab978681ec83d6ab1a7.
def localCycle00101 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false, true] }
  origin := ![.thetaNext 1, .corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b3a7f7cbf6f755ae9f52a074d321b8ad2dc3d90cd7b342a42a92e4e0cb05b245.
def localCycle00102 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 5, .corridorUpper 0 1, .triangle 1 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint b7f1c37da33f071a116f7bd608a6b0d8ac44726c03b34e01cc8acdea42adb981.
def localCycle00103 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6, .distance 1 2]
    constant := ![0, -2, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint b8540531183ffde16987227832c71a9d997cd613178ac245e8465caffd35afcb.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 1 1, .triangle 20 2, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint b8d66862cc330790161061c9d02bd4b3494ba6459f3261a4257ebc71860e981f.
def localCycle00105 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint b9049de66e453e7b6487bc8da4d6db4b479ce707f8781603deceba99849cd56d.
def localCycle00106 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 2]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint ba5166dab306d821a7566de39d016c1f114b7f9cdde88f8cc9b9f058335079dc.
def localCycle00107 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 21 1, .triangle 15 1, .triangle 16 2, .gapLower 1 0, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint baacf551c61fdfdff7a062f219dcd728c3b8292e71a177a0d66514fba13d13f0.
def localCycle00108 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint bb0496a0b2787c04c7041457e60c9f9aa2baeffdc514a1e0a0fff6a88edf8ed5.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6]
    constant := ![-2, 0, 0, -2, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 17 1, .triangle 16 2, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2]

-- Cycle fingerprint bb20e2e6df5c3ed4a5c4d8350dfecdf27ea3606fc30242eefb538943370be031.
def localCycle00110 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint bcd8bfed084ebd5cf3d9251690cf19104a0cae07d9c6c7b02d4f753e506cf2f2.
def localCycle00111 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 1 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint bcdf70f47a8847bfee3d2e0f15587f9bb5abdc59c8a3afc901a2a7d1bc0f5c31.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1]
    constant := ![0, 0, 2, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 21 1, .gapLower 1 3, .triangle 17 1, .gapLower 1 1, .corridorLower 1 4]

-- Cycle fingerprint c02a81beafaaf4f3ef59b8eb529f1a602d3ce64cc9c5517c187479835cc75e64.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6]
    constant := ![-1, -1, 0, -1, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0]

-- Cycle fingerprint c0f39e2ea1dd6d824861d0217bae00782877f5f364fe64b0d58cb4d584e516b7.
def localCycle00114 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 4, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint c27512d80ebd0e24954f2b92338b708ae4a5b86e732fddc6fc4a79121f134ce7.
def localCycle00115 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint c39291d2b8aa1519be421ad7ebaa8cfd8301827ce438e4b802ce91c92810cfed.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero, .theta 6, .distance 1 6]
    constant := ![0, -2, -2, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 21 1, .gapLower 1 3, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint c5bcc67cb5040c7cf9b9b21f072c044f6f607a723f498975af03492003925439.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint c634b4d5f4ee7af9add01e43e954cc400cbf06eadc8d86772bf916f5a4f5a495.
def localCycle00118 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, -1, 0, 0, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true, false, true, true, false, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .triangle 3 2]

-- Cycle fingerprint c75ccec9cbf9bcd56a9482873b2b4589074638e23c94cb511298660e7b1706fa.
def localCycle00119 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 0, 0, 3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .thetaLower 3, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0]

-- Cycle fingerprint c804285934bbbf79f0bf81503a8e27ea6823f2ba2f29487827d05d6379a06be3.
def localCycle00120 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint c92aac6b67d61d07a24045afad2ddc16bcaf730eec91382511cb613db5e0706c.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .triangle 16 2, .gapLower 1 0]

-- Cycle fingerprint c96066834cc591e5d956b731cc8d6e5db4d9f09afdad24b434665e4efe016f01.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -2, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint c9a82104974c7120170cf13863d3f84c8f09cb41f6ff2e54399ea1290733ac85.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 33 2, .corridorLower 3 6]

-- Cycle fingerprint c9f581cef3edf1c3821808247c868b4ee99f2a5e0a090113ab37d635b4c87cb4.
def localCycle00124 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 20 1, .triangle 21 2, .triangle 23 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint cb2ce48e15f3a56ee4dce6e408187093b6c0100559c363a143d49fe49e8dcb71.
def localCycle00125 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 1 1, .triangle 15 1, .triangle 16 0, .corridorLower 2 4, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint cc060dce73c8fd118a3a1465d0ec3d57283f496b4f70a412459a226eba82dcad.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint ce6e1abf79aa021d92ba330e85f531211cd884fd739f128dbd396ed26da25d65.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6]
    constant := ![0, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false] }
  origin := ![.triangle 32 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 20 1, .triangle 21 0]

-- Cycle fingerprint d29091940fc6b754037bbbdff48bd1c5620e14985facc2549096ddfd21ccbae4.
def localCycle00128 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint d4aa8b8639d5becbfe8d73367e290cbf0c839bbab7cb77444f6452dfbd6f4ab7.
def localCycle00129 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint d6e97cc3fc4f0f96dd56ee64a7ed3a8ba33ef6516976f5f8470460f6f7115be9.
def localCycle00130 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 3]
    constant := ![-2, 0, -2, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 22 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 21 1]

-- Cycle fingerprint d87113779d85299490b6145a58940745d681a282431a00fb8e2c96319ce3fcb9.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 3 5]
    constant := ![-1, -1, 0, 0, -1, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 0]

-- Cycle fingerprint d9035f6f0d880a2e7a7f4e93e5f9990df9468d5959347bffe77a97892b7ffbf4.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 18 1, .triangle 16 0]

-- Cycle fingerprint d9fcfc347b4d55d2c8d06e8589d726abc7a7615eaa4f6f2263b35fcb6528c11f.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 2, .distance 1 4, .theta 1]
    constant := ![2, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 20 1, .triangle 21 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 4]

-- Cycle fingerprint db8840e5159cf6c8c66722271a265679160a81796dd3c59e86e8e6a5cdf8d877.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6]
    constant := ![0, -1, -1, 0, 1, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 16 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 3 0, .triangle 20 1, .triangle 21 2]

-- Cycle fingerprint dd3f30da600ef378947f03e50385ae259cf726d9fe93f3db024223624ab2912c.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3, .distance 2 3, .distance 0 2, .distance 2 4]
    constant := ![-1, -1, 0, -1, 0, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 17 0, .triangle 26 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 5 0, .triangle 6 0]

-- Cycle fingerprint de4a1845900c09f6df105da9c94ee87edfb34bf4db2c1c0e8b9114b8c4563450.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint e102140268c7c192e5c99e14ed363a90ecc3fa1c8353e750f54f2f40d42f5288.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .corridorLower 5 6]

-- Cycle fingerprint e37e5cdd99dcee94e1ed35639aee87ee32830d60b128eead6aa24b8ce04ca703.
def localCycle00138 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 5, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint e5349eaaf505208ff699916e272fd43ff245b7ce79a874d6692fd23c0b0e158d.
def localCycle00139 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .gapLower 1 3, .corridorLower 1 5]

-- Cycle fingerprint e711f03628f672c450127d57dda5221f5c0e4e2ca9f96c262827658164e422f7.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint e7d7c7ce26e44817b4e75668ec4b8712ef4af6796ad261b7358a39eff415a6fb.
def localCycle00141 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -1, 0, -1, 0, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, true, true, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 2]

-- Cycle fingerprint ebe29de6adfb59872edc151eaaf752020abb81c59b8c2dd0d90372167145446e.
def localCycle00142 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 15 1, .triangle 16 2, .triangle 23 0, .triangle 29 0, .corridorLower 2 4, .thetaNext 1]

-- Cycle fingerprint ec5af9aaf545a1feb09b4354bfb04538691778641fb3c26dd99290015a452bfb.
def localCycle00143 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, 0, -3, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false] }
  origin := ![.triangle 3 0, .triangle 20 1, .triangle 21 2, .triangle 23 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint ed5617c5261f8853880555e14dfded0403c5b2df91ec75abbdc576c27c54df72.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6]
    constant := ![-2, -1, -1, 0, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 16 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 3 0, .triangle 20 1, .triangle 21 2]

-- Cycle fingerprint ed9bbb0fb72f9c2a0dc5d3d895f8df731f43b69ae419359d9d5c7c0b93e97007.
def localCycle00145 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 3, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 4, .corridorLower 1 3]

-- Cycle fingerprint ee4eb0f74ea33b97696bf763f62c31c9217f0b8bf0c2ac4e5b5fde3888699353.
def localCycle00146 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint eea4b064f2026d95c34b5234626e0100d8c5528e1204406e8debf10731b25efa.
def localCycle00147 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 20 1, .triangle 21 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 4, .corridorUpper 0 1]

-- Cycle fingerprint ef1317859db8144c930a87038024026c87a7b17249282a31eeb6010e4353162f.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6]
    constant := ![-2, 0, -2, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 16 2, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 21 2]

-- Cycle fingerprint ef93265b4f9ebc3200c93e2bb95c3569a2465bc567857cf1293776b06a9c0f7d.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 15 1, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint f03b61f80f979553329ace9161adeb2fb68e67090e7b91103d2cc95f540554ca.
def localCycle00150 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint f1bfbc50176f527176e607d42064a8c61ab05172503293f6d9e8124ad1934dd0.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint f4a4bfdae8b2b8d7d8f62af23c3573f516b78a28a0086d47265025ab3c87043b.
def localCycle00152 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint f537e526488e16521e93f995b99c1b7a5e3b01ffc846488c695144c98a324eab.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero, .theta 6]
    constant := ![2, -2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false, false, false] }
  origin := ![.gapUpper 6 0, .gapLower 1 4, .triangle 20 2, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3, .thetaUpper 6]

-- Cycle fingerprint f8a865bddac48a646a9de441af5368e00e38bc0203574004b7423f1fb199b9ba.
def localCycle00154 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint ffd7b45055cdc61e417c0c07aea2bf6f9ca1e58a5a4fa5b66a0e3b652b8910a1.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .gapLower 2 0]

def library : Library := fun id => if id < 78 then (if id < 39 then (if id < 19 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 14 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)))) else (if id < 16 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))))) else (if id < 29 then (if id < 24 then (if id < 21 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))))) else (if id < 34 then (if id < 31 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))))) else (if id < 58 then (if id < 48 then (if id < 43 then (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))))) else (if id < 53 then (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))) else (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))))) else (if id < 68 then (if id < 63 then (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))) else (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))))) else (if id < 73 then (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))))))) else (if id < 117 then (if id < 97 then (if id < 87 then (if id < 82 then (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))))) else (if id < 92 then (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))) else (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))))) else (if id < 107 then (if id < 102 then (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)))) else (if id < 104 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))))) else (if id < 112 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))) else (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))))))) else (if id < 136 then (if id < 126 then (if id < 121 then (if id < 119 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none))) else (if id < 123 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))))) else (if id < 131 then (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))) else (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)))))) else (if id < 146 then (if id < 141 then (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)))) else (if id < 143 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))))) else (if id < 151 then (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)))) else (if id < 153 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![5, 2, 6, 4, 3, 0], ![5, 1, 6, 4, 0, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 6, 1, 2, 0], ![4, 3, 2, 1, 0, 6], ![3, 4, 1, 2, 0, 5]], proof := .tail 129 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19968)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![5, 2, 6, 4, 3, 0], ![5, 1, 6, 4, 0, 3], ![5, 6, 4, 1, 0, 2], ![5, 6, 3, 1, 2, 0], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 78 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19969)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![5, 6, 2, 4, 3, 0], ![5, 6, 1, 4, 0, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 6, 1, 2, 0], ![4, 3, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 5]], proof := .tail 140 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19970)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![5, 6, 2, 4, 3, 0], ![5, 6, 1, 4, 0, 3], ![5, 6, 4, 1, 0, 2], ![5, 6, 3, 1, 2, 0], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 64 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19971)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 2, 4, 3, 6, 0], ![5, 1, 4, 6, 0, 3], ![5, 4, 1, 6, 0, 2], ![5, 3, 1, 2, 6, 0], ![4, 3, 2, 1, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 60 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19972)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 2, 4, 3, 6, 0], ![5, 1, 6, 4, 0, 3], ![5, 4, 1, 6, 0, 2], ![5, 3, 1, 6, 2, 0], ![4, 3, 2, 1, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 135 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19973)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 2, 4, 6, 3, 0], ![5, 1, 4, 6, 0, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 1, 2, 6, 0], ![4, 3, 2, 1, 6, 0], ![3, 1, 2, 4, 5, 0]], proof := .tail 60 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19974)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 2, 4, 6, 3, 0], ![5, 1, 6, 4, 0, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 1, 6, 2, 0], ![4, 3, 2, 1, 6, 0], ![3, 1, 4, 2, 5, 0]], proof := .tail 135 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19975)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 2, 6, 4, 3, 0], ![5, 1, 6, 4, 0, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 6, 1, 2, 0], ![4, 3, 2, 1, 6, 0], ![3, 4, 1, 2, 5, 0]], proof := .tail 129 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19976)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 2, 6, 4, 3, 0], ![5, 1, 6, 4, 0, 3], ![5, 6, 4, 1, 0, 2], ![5, 6, 3, 1, 2, 0], ![4, 3, 2, 1, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 78 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19977)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 6, 2, 4, 3, 0], ![5, 6, 1, 4, 0, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 6, 1, 2, 0], ![4, 3, 2, 1, 6, 0], ![3, 4, 2, 1, 5, 0]], proof := .tail 140 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19978)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 5, 2, 4, 3, 0], ![5, 6, 1, 4, 0, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 6, 1, 2, 0], ![4, 3, 2, 6, 1, 0], ![3, 4, 2, 5, 1, 0]], proof := .tail 155 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19979)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 5, 2, 4, 3, 0], ![6, 5, 1, 4, 0, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 6, 1, 2, 0], ![4, 3, 6, 2, 1, 0], ![3, 4, 5, 2, 1, 0]], proof := .tail 59 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19980)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 6, 2, 4, 3, 0], ![5, 6, 1, 4, 0, 3], ![5, 6, 4, 1, 0, 2], ![5, 6, 3, 1, 2, 0], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 64 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19981)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 5, 2, 4, 3, 0], ![5, 6, 1, 4, 0, 3], ![5, 6, 4, 1, 0, 2], ![5, 6, 3, 1, 2, 0], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 155 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19982)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 5, 2, 4, 3, 0], ![6, 5, 1, 4, 0, 3], ![5, 6, 4, 1, 0, 2], ![5, 6, 3, 1, 2, 0], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 59 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19983)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 5, 2, 4, 3, 0], ![6, 5, 1, 4, 0, 3], ![6, 5, 4, 1, 0, 2], ![5, 6, 3, 1, 2, 0], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 14 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19984)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 5, 2, 4, 3, 0], ![6, 5, 1, 4, 0, 3], ![6, 5, 4, 1, 0, 2], ![6, 5, 3, 1, 2, 0], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 123 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19985)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 2, 1, 0, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 56 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19986)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 2, 1, 0, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 39 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19987)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 3, 5, 6], ![4, 1, 0, 2, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 114 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19988)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 67 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19989)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![4, 2, 3, 6, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 118 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19990)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![4, 2, 3, 6, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 67 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19991)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 2, 1, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 3, 2, 4]], proof := .tail 61 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19992)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![4, 2, 3, 6, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 2, 1, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 3, 2, 4]], proof := .tail 76 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19993)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![4, 2, 3, 6, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 62 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19994)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![4, 2, 6, 3, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 6, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 2, 1, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 0, 2, 4]], proof := .tail 50 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19995)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![4, 2, 6, 3, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 0, 6, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 50 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19996)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![4, 2, 6, 3, 5, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 0, 6, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 0, 2, 4]], proof := .low (![143, 52, 84, 115, 73, 32, 134, 1, 148, 29, 92, 21, 124, 72, 65, 92, 147, 133, 106, 92, 26, 144, 92, 17, 58, 92, 92, 127]) }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19997)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 2, 1, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 85 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19998)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 85 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19999)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 85 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20000)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 74 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20001)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 2, 1, 6, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 96 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20002)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 2, 1, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 96 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20003)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 2, 1, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 96 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20004)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 2, 1, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 137 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20005)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![6, 4, 2, 3, 5, 0], ![4, 6, 1, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 2, 6, 1, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 91 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20006)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 6, 2, 1, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 146 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20007)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 0, 3, 5], ![6, 4, 1, 0, 2, 5], ![6, 3, 2, 1, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 38 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20008)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 2, 1, 0, 5, 6], ![1, 0, 3, 2, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 125 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20009)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 2, 1, 0, 6, 5], ![1, 0, 3, 2, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 12 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20010)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 5, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 2, 1, 0, 5, 6], ![1, 0, 3, 2, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 69 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20011)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 5, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 2, 1, 0, 6, 5], ![1, 0, 3, 2, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 28 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20012)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 6, 5, 3], ![4, 1, 0, 5, 6, 2], ![3, 2, 1, 0, 6, 5], ![1, 0, 3, 6, 2, 4], ![1, 0, 3, 5, 2, 4]], proof := .tail 113 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20013)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 2, 1, 0, 6, 5], ![1, 0, 6, 3, 2, 4], ![1, 0, 5, 3, 2, 4]], proof := .tail 77 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20014)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![4, 2, 3, 6, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 2, 1, 0, 6, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 0, 3, 2, 4]], proof := .tail 131 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20015)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![4, 2, 3, 6, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 0, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 33 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20016)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![4, 2, 6, 3, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 6, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 2, 1, 0, 6, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 3, 0, 2, 4]], proof := .tail 23 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20017)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![4, 2, 6, 3, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 0, 6, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 23 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20018)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![4, 2, 6, 3, 5, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 0, 6, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 49 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20019)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 0, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 2, 1, 0, 6, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 23 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20020)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 0, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 23 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20021)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 0, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 117 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20022)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 0, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 49 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20023)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 0, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 2, 1, 6, 0, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 3 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20024)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 0, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 2, 1, 6, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 3 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20025)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 0, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 2, 1, 6, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 18 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20026)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 0, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 2, 1, 6, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 16 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20027)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![6, 4, 2, 3, 5, 0], ![4, 6, 1, 0, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 2, 6, 1, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 34 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20028)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 0, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 6, 2, 1, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 30 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20029)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 0, 5, 3], ![6, 4, 1, 0, 5, 2], ![6, 3, 2, 1, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 108 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20030)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 5, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 2, 1, 0, 5, 6], ![1, 3, 0, 2, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 119 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20031)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 5, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 2, 1, 0, 6, 5], ![1, 3, 0, 2, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 152 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20032)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 5, 6, 3], ![4, 1, 5, 0, 6, 2], ![3, 2, 1, 0, 5, 6], ![1, 3, 0, 2, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 151 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20033)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 5, 6, 3], ![4, 1, 5, 0, 6, 2], ![3, 2, 1, 0, 6, 5], ![1, 3, 0, 2, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 151 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20034)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 6, 5, 3], ![4, 1, 5, 0, 6, 2], ![3, 2, 1, 0, 6, 5], ![1, 3, 0, 6, 2, 4], ![1, 0, 3, 5, 2, 4]], proof := .tail 128 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20035)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 5, 6, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 0, 5, 6], ![1, 3, 0, 2, 4, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 8 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20036)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 5, 6, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![1, 3, 0, 2, 6, 4], ![1, 3, 0, 2, 5, 4]], proof := .tail 8 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20037)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 6, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![1, 3, 0, 6, 2, 4], ![1, 3, 0, 5, 2, 4]], proof := .tail 113 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20038)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 6, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 0, 2, 4]], proof := .tail 22 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20039)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 0, 6, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 2, 1, 0, 6, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 0, 2, 4]], proof := .tail 6 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20040)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 0, 6, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 101 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20041)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 0, 6, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 89 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20042)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 0, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 83 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20043)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 0, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 2, 1, 0, 6, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 117 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20044)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 0, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 117 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20045)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 0, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 117 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20046)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 0, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 89 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20047)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 0, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 6, 0, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 2, 4, 0]], proof := .tail 154 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20048)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 0, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 2, 1, 6, 0, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 18 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20049)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 0, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 2, 1, 6, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 18 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20050)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 0, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 1, 6, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 18 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20051)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 0, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 1, 6, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 57 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20052)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![6, 4, 2, 3, 5, 0], ![4, 6, 1, 0, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 6, 1, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 142 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20053)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 0, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 6, 2, 1, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 98 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20054)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 0, 5, 3], ![6, 4, 1, 5, 0, 2], ![6, 3, 2, 1, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 9 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20055)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 0, 5, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 0, 5, 6], ![3, 1, 0, 2, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![24, 52, 55, 70, 7, 13, 88, 36, 15, 130, 0, 103, 107, 82, 112, 2, 87, 25, 116, 153, 11, 53, 138, 94, 71, 4, 145, 132]) }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20056)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 0, 5, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 0, 6, 5], ![3, 1, 0, 2, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 110 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20057)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 0, 5, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 2, 1, 0, 5, 6], ![3, 1, 0, 2, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 104 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20058)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 0, 5, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 0, 2, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 20 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20059)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 0, 6, 5, 3], ![4, 5, 1, 0, 6, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 0, 6, 2, 4], ![1, 0, 3, 5, 2, 4]], proof := .tail 68 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20060)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 0, 5, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 5, 6], ![3, 1, 0, 2, 4, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 37 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20061)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 0, 5, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 0, 2, 6, 4], ![1, 3, 0, 2, 5, 4]], proof := .tail 100 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20062)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 0, 6, 5, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 0, 6, 2, 4], ![1, 3, 0, 5, 2, 4]], proof := .tail 19 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20063)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 0, 6, 5, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 6, 0, 2, 4], ![1, 3, 5, 0, 2, 4]], proof := .tail 35 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20064)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 0, 5, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 5, 6], ![3, 1, 0, 2, 4, 6], ![3, 1, 0, 2, 4, 5]], proof := .low (![81, 52, 40, 139, 75, 48, 47, 122, 86, 109, 111, 80, 121, 42, 97, 54, 44, 31, 120, 93, 141, 66, 102, 51, 46, 41, 105, 95]) }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20065)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 0, 5, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 0, 2, 6, 4], ![3, 1, 0, 2, 5, 4]], proof := .tail 79 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20066)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 0, 6, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 0, 6, 2, 4], ![3, 1, 0, 5, 2, 4]], proof := .tail 63 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20067)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 0, 6, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 6, 0, 2, 4], ![3, 1, 5, 0, 2, 4]], proof := .tail 35 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20068)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 0, 6, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 6, 1, 0, 2, 4], ![3, 5, 1, 0, 2, 4]], proof := .tail 126 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20069)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 0, 6, 5, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 3, 1, 0, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 5 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20070)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 6, 0, 5, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 6, 0, 2, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 117 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20071)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 6, 0, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 6, 0, 2, 4], ![3, 1, 5, 2, 0, 4]], proof := .tail 117 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20072)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 0, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 6, 1, 0, 2, 4], ![3, 5, 1, 2, 0, 4]], proof := .tail 117 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20073)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 0, 5, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 3, 1, 0, 2, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 117 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20074)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 0, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 6, 1, 0, 2, 4], ![3, 5, 2, 1, 0, 4]], proof := .tail 27 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20075)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 0, 5, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 3, 1, 0, 2, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 5 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20076)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 6, 0, 5, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 1, 6, 0, 2, 4], ![1, 3, 5, 2, 4, 0]], proof := .tail 18 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20077)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 6, 0, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 1, 6, 0, 2, 4], ![3, 1, 5, 2, 4, 0]], proof := .tail 18 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20078)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 0, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 6, 1, 0, 2, 4], ![3, 5, 1, 2, 4, 0]], proof := .tail 18 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20079)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 0, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 6, 1, 0, 2, 4], ![3, 5, 2, 1, 4, 0]], proof := .tail 43 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20080)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![6, 4, 2, 5, 3, 0], ![4, 6, 1, 0, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 6, 1, 0, 5], ![3, 6, 1, 0, 2, 4], ![3, 5, 2, 4, 1, 0]], proof := .tail 136 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20081)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 0, 5, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![6, 3, 1, 0, 2, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 18 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20082)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 0, 5, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![6, 3, 1, 0, 2, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 16 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20083)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![6, 4, 2, 5, 3, 0], ![4, 6, 1, 0, 5, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 6, 1, 0, 5], ![6, 3, 1, 0, 2, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 149 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20084)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![6, 4, 2, 5, 3, 0], ![6, 4, 1, 0, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 6, 2, 1, 0, 5], ![3, 6, 1, 0, 2, 4], ![3, 5, 4, 2, 1, 0]], proof := .tail 30 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20085)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![6, 4, 2, 5, 3, 0], ![6, 4, 1, 0, 5, 3], ![4, 6, 5, 1, 0, 2], ![3, 6, 2, 1, 0, 5], ![6, 3, 1, 0, 2, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 30 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20086)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![6, 4, 2, 5, 3, 0], ![6, 4, 1, 0, 5, 3], ![6, 4, 5, 1, 0, 2], ![6, 3, 2, 1, 0, 5], ![6, 3, 1, 0, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 99 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20087)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 0, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 2, 1, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 10 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20088)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 0, 6, 3], ![4, 1, 5, 0, 6, 2], ![3, 2, 1, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 45 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20089)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![4, 5, 2, 6, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 0, 6, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 45 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20090)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 0, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 2, 1, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 150 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20091)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 0, 6, 3], ![4, 1, 5, 0, 6, 2], ![3, 2, 1, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 45 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20092)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![4, 5, 2, 6, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 0, 6, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 3, 0, 2, 5, 4]], proof := .tail 45 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20093)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 90 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20094)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 3, 2, 0, 5, 4]], proof := .tail 90 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20095)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (19968 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 19968 ≤ id.val) (hhigh : id.val < 20096) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 19968)) = true := by
  let j : Fin 128 := ⟨id.val - 19968, by omega⟩
  have hsum : 19968 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (19968 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard156
