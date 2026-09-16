/-
This file defines the curve-membership table.
-/

import Construction.ArgoMAC.DigitAdaptor
import Construction.ArgoMAC.Input

namespace Kriterion.ArgoMAC.CurveMembership

open BN254

/-- Each adaptor has one fixed-key window family. -/
structure Oracles where
  y4 : Nat → BitAdaptor.FixedKeyOracle
  y6 : Nat → BitAdaptor.FixedKeyOracle
  x3 : Nat → BitAdaptor.FixedKeyOracle
  x5 : Nat → BitAdaptor.FixedKeyOracle
  x7 : Nat → BitAdaptor.FixedKeyOracle

/-- This is the curve-membership table. -/
structure Table where
  c0 : BaseField
  c1 : BaseField
  c2 : BaseField
  x3 : Vector BitAdaptor.Table coordinateBitCount
  x5 : Vector BitAdaptor.Table coordinateBitCount
  x7 : Vector BitAdaptor.Table coordinateBitCount
  y4 : Vector BitAdaptor.Table coordinateBitCount
  y6 : Vector BitAdaptor.Table coordinateBitCount

def evaluateDigit (windows : Nat → BitAdaptor.FixedKeyOracle)
    (table : Vector BitAdaptor.Table coordinateBitCount) (value : BaseField)
    (inputMac : CoordinateMac) : BaseField :=
  DigitAdaptor.fromBits fun index =>
    (DigitAdaptor.evaluate windows (coordinateValues value) table inputMac).get index

theorem evaluateDigitGarbleEncode (windows : Nat → BitAdaptor.FixedKeyOracle)
    (slope : BaseField) (key : CoordinateMacKey) (value : BaseField) :
    evaluateDigit windows (DigitAdaptor.garble windows slope key).1 value
        (encodeCoordinate key (coordinateBits value)) =
      slope * value + DigitAdaptor.bitsK (DigitAdaptor.garble windows slope key).2 := by
  rw [evaluateDigit, show encodeCoordinate key (coordinateBits value) =
    DigitAdaptor.encode key (coordinateValues value) from rfl]
  rw [DigitAdaptor.evaluateValueGarbleEncode, coordinateBitValue]

/-- The garbler samples `r1` and `r2`. The adaptors derive `r3` through `r7`. -/
def garble (bridgeKey mask r1 r2 : BaseField) (oracles : Oracles)
    (inputKey : InputMacKey) : Table :=
  let y4 := DigitAdaptor.garble oracles.y4 (-r2) inputKey.y
  let r4 := DigitAdaptor.bitsK y4.2
  let y6 := DigitAdaptor.garble oracles.y6 (-r4) inputKey.y
  let r6 := DigitAdaptor.bitsK y6.2
  let x3 := DigitAdaptor.garble oracles.x3 (-r1) inputKey.x
  let r3 := DigitAdaptor.bitsK x3.2
  let x5 := DigitAdaptor.garble oracles.x5 (-r3) inputKey.x
  let r5 := DigitAdaptor.bitsK x5.2
  let x7 := DigitAdaptor.garble oracles.x7 (-r5) inputKey.x
  let r7 := DigitAdaptor.bitsK x7.2
  { c0 := 3 * mask + bridgeKey - r6 - r7
    c1 := mask + r1
    c2 := -mask + r2
    x3 := x3.1
    x5 := x5.1
    x7 := x7.1
    y4 := y4.1
    y6 := y6.1 }

def evaluate (oracles : Oracles) (table : Table) (input : AffineInput)
    (inputMac : InputMac) : BaseField :=
  let c3 := evaluateDigit oracles.x3 table.x3 input.x inputMac.x
  let c4 := evaluateDigit oracles.y4 table.y4 input.y inputMac.y
  let c5 := evaluateDigit oracles.x5 table.x5 input.x inputMac.x
  let c6 := evaluateDigit oracles.y6 table.y6 input.y inputMac.y
  let c7 := evaluateDigit oracles.x7 table.x7 input.x inputMac.x
  table.c0 + table.c1 * input.x ^ 3 + table.c2 * input.y ^ 2 +
    c3 * input.x ^ 2 + c4 * input.y + c5 * input.x + c6 + c7

/-- Correct labels produce the membership polynomial. -/
theorem evaluateEncoded (bridgeKey mask r1 r2 : BaseField) (oracles : Oracles)
    (inputKey : InputMacKey) (input : AffineInput) :
    evaluate oracles (garble bridgeKey mask r1 r2 oracles inputKey)
        input (inputKey.encodeAffine input) =
      bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2) := by
  simp only [evaluate, garble, InputMacKey.encodeAffine, InputMacKey.encode,
    BitInput.ofAffine]
  rw [evaluateDigitGarbleEncode, evaluateDigitGarbleEncode,
    evaluateDigitGarbleEncode, evaluateDigitGarbleEncode,
    evaluateDigitGarbleEncode]
  ring

/-- Correct labels release `t` for an on-curve input. -/
theorem evaluateEncodedOnCurve (bridgeKey mask r1 r2 : BaseField) (oracles : Oracles)
    (inputKey : InputMacKey) (input : AffineInput) (inputOnCurve : OnCurve input) :
    evaluate oracles (garble bridgeKey mask r1 r2 oracles inputKey)
      input (inputKey.encodeAffine input) = bridgeKey := by
  rw [evaluateEncoded]
  rw [show input.x ^ 3 + 3 - input.y ^ 2 = 0 by rw [inputOnCurve]; ring]
  ring

end Kriterion.ArgoMAC.CurveMembership
