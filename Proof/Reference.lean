/-
This file defines the reference sample space of the steering-invisibility proof
and the static change of coordinates that lets the hidden randomness be sampled
after the adversary chooses its input.

The reference table is built from fresh per-gate secrets: one field element in
place of the Davies--Meyer hash of the false label and one 256-bit pad in place
of the pad of the true label. The secret oracle ignores the label, so the
reference table does not depend on the label key.

For one fixed input, the raw coordinates `(mask, r1, r2, hash, pad)` are in
bijection with the middle coordinates `(mask, c1, c2, selected outputs, rows)`,
and the released row `c0` is affine in the mask with coefficient
`x^3 + 3 - y^2`. Off the curve the coefficient is nonzero, so the visible data
`(c0, c1, c2, rows, selected outputs)` is uniform and independent of the bridge
key. On the curve the coefficient vanishes, and shifting the selected output of
adaptor `x7` at position `0` moves the visible law of one bridge key to the
visible law of another.

The file also proves the arithmetic tail of the obligation: a per-query
constant up to `2^28` over `2^128` plus a one-time term up to `2^-101` stays
below one unit of work per query over `2^100`.
-/

import Proof.Steering

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

/-! ### The arithmetic tail -/

/-- Any error below `K q / 2^128 + ε₀` with `K ≤ 2^28` and `ε₀ ≤ 2^-101` is one unit of
work per query over `2^100`. -/
theorem workPerAdvantage_of_le (queries : Nat) (perQuery oneTime error : ℝ)
    (perQueryLe : perQuery ≤ 2 ^ 28)
    (oneTimeLe : oneTime ≤ 1 / 2 ^ 101)
    (bound : error ≤ perQuery * queries / 2 ^ 128 + oneTime) :
    Cryptography.Assumptions.WorkPerAdvantage 100 (queries + 1) error := by
  unfold Cryptography.Assumptions.WorkPerAdvantage
  push_cast
  have queriesNonneg : (0 : ℝ) ≤ queries := Nat.cast_nonneg queries
  have perQueryTerm : perQuery * queries / 2 ^ 128 * 2 ^ 100 ≤ (queries : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc perQuery * queries * 2 ^ 100 ≤ 2 ^ 28 * queries * 2 ^ 100 := by
          gcongr
      _ = (queries : ℝ) * 2 ^ 128 := by ring
  have oneTimeTerm : oneTime * 2 ^ 100 ≤ 1 := by
    calc oneTime * 2 ^ 100 ≤ (1 : ℝ) / 2 ^ 101 * 2 ^ 100 := by gcongr
      _ ≤ 1 := by norm_num
  calc error * 2 ^ 100 ≤ (perQuery * queries / 2 ^ 128 + oneTime) * 2 ^ 100 := by gcongr
    _ = perQuery * queries / 2 ^ 128 * 2 ^ 100 + oneTime * 2 ^ 100 := by ring
    _ ≤ queries + 1 := add_le_add perQueryTerm oneTimeTerm

/-- Every advantage is at most one. -/
theorem advantage_le_one (first second : PMF Bool) :
    Cryptography.Assumptions.advantage first second ≤ 1 := by
  unfold Cryptography.Assumptions.advantage
  have firstLe : (first true).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp)
  have secondLe : (second true).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp)
  rw [abs_le]
  constructor <;> linarith [ENNReal.toReal_nonneg (a := first true),
    ENNReal.toReal_nonneg (a := second true)]

/-! ### Fresh gate secrets -/

/-- One gate's secret oracle: a fixed hash value and a fixed pad. It ignores the label. -/
def secretOracle (hash : BaseField) (pad : BitAdaptor.Ciphertext) : BitAdaptor.FixedKeyOracle where
  hashToField _ := hash
  encrypt _ message := pad ^^^ BitAdaptor.fieldBytes message
  decrypt _ ciphertext := (pad ^^^ ciphertext).toNat
  decryptEncrypt _ message := by
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    simp only [BitAdaptor.fieldBytes, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (lt_trans message.val_lt (by decide))]
    exact ZMod.natCast_zmod_val message

/-- One value for every gate: five adaptor families times the coordinate bit positions. -/
abbrev GateValues (Value : Type) := CurveAdaptor → Fin coordinateBitCount → Value

/-- The secret window family of one adaptor. -/
def secretWindows (hash : GateValues BaseField) (pad : GateValues BitAdaptor.Ciphertext)
    (adaptor : CurveAdaptor) (position : Nat) : BitAdaptor.FixedKeyOracle :=
  secretOracle (hash adaptor ⟨position % coordinateBitCount, Nat.mod_lt _ (by decide)⟩)
    (pad adaptor ⟨position % coordinateBitCount, Nat.mod_lt _ (by decide)⟩)

theorem secretWindows_val (hash : GateValues BaseField) (pad : GateValues BitAdaptor.Ciphertext)
    (adaptor : CurveAdaptor) (position : Fin coordinateBitCount) :
    secretWindows hash pad adaptor position.val =
      secretOracle (hash adaptor position) (pad adaptor position) := by
  have same : (⟨position.val % coordinateBitCount, Nat.mod_lt _ (by decide)⟩ :
      Fin coordinateBitCount) = position :=
    Fin.ext (Nat.mod_eq_of_lt position.isLt)
  simp only [secretWindows, same]

/-- The secret oracles of the reference table. -/
def secretOracles (hash : GateValues BaseField) (pad : GateValues BitAdaptor.Ciphertext) :
    CurveMembership.Oracles where
  y4 := secretWindows hash pad .y4
  y6 := secretWindows hash pad .y6
  x3 := secretWindows hash pad .x3
  x5 := secretWindows hash pad .x5
  x7 := secretWindows hash pad .x7

/-- The raw coordinates of the reference table. The same type also carries the middle
coordinates `(mask, c1, c2, selected outputs, rows)` of one input. -/
@[ext] structure Coordinates where
  mask : BaseField
  r1 : BaseField
  r2 : BaseField
  hash : GateValues BaseField
  pad : GateValues BitAdaptor.Ciphertext

/-- The reference table of one bridge key. The secret oracles ignore the label key. -/
def Coordinates.table (bridgeKey : BaseField) (key : InputMacKey) (raw : Coordinates) :
    CurveMembership.Table :=
  CurveMembership.garble bridgeKey raw.mask raw.r1 raw.r2 (secretOracles raw.hash raw.pad) key

/-- The slope of each adaptor family, from the sampled values and the hash secrets. -/
def slopeOf (r1 r2 : BaseField) (hash : GateValues BaseField) : CurveAdaptor → BaseField
  | .y4 => -r2
  | .y6 => -DigitAdaptor.fromBits (hash .y4)
  | .x3 => -r1
  | .x5 => -DigitAdaptor.fromBits (hash .x3)
  | .x7 => -DigitAdaptor.fromBits (hash .x5)

/-- The slope of each adaptor family in the reference table. -/
def Coordinates.slope (raw : Coordinates) : CurveAdaptor → BaseField :=
  slopeOf raw.r1 raw.r2 raw.hash

/-- The rows of one adaptor family of a table. -/
def tableRows (table : CurveMembership.Table) :
    CurveAdaptor → Vector BitAdaptor.Table coordinateBitCount
  | .y4 => table.y4
  | .y6 => table.y6
  | .x3 => table.x3
  | .x5 => table.x5
  | .x7 => table.x7

/-- The key sum of a secret-oracle adaptor is the sum of its hash secrets. -/
theorem bitsK_secretWindows (hash : GateValues BaseField) (pad : GateValues BitAdaptor.Ciphertext)
    (adaptor : CurveAdaptor) (slope : BaseField) (keys : CoordinateMacKey) :
    DigitAdaptor.bitsK (DigitAdaptor.garble (secretWindows hash pad adaptor) slope keys).2 =
      DigitAdaptor.fromBits (hash adaptor) := by
  unfold DigitAdaptor.bitsK
  congr 1
  funext index
  simp [DigitAdaptor.garble, BitAdaptor.garble, secretWindows_val, secretOracle]

/-- The rows of a secret-oracle adaptor. -/
theorem garble_secretWindows_row (hash : GateValues BaseField)
    (pad : GateValues BitAdaptor.Ciphertext) (adaptor : CurveAdaptor) (slope : BaseField)
    (keys : CoordinateMacKey) (index : Fin coordinateBitCount) :
    (DigitAdaptor.garble (secretWindows hash pad adaptor) slope keys).1.get index =
      ⟨pad adaptor index ^^^ BitAdaptor.fieldBytes (slope + hash adaptor index)⟩ := by
  simp [DigitAdaptor.garble, BitAdaptor.garble, BitAdaptor.OutputKey.encode, secretWindows_val,
    secretOracle]

theorem Coordinates.table_c1 (bridgeKey : BaseField) (key : InputMacKey) (raw : Coordinates) :
    (raw.table bridgeKey key).c1 = raw.mask + raw.r1 := rfl

theorem Coordinates.table_c2 (bridgeKey : BaseField) (key : InputMacKey) (raw : Coordinates) :
    (raw.table bridgeKey key).c2 = -raw.mask + raw.r2 := rfl

theorem Coordinates.table_c0 (bridgeKey : BaseField) (key : InputMacKey) (raw : Coordinates) :
    (raw.table bridgeKey key).c0 =
      3 * raw.mask + bridgeKey - DigitAdaptor.fromBits (raw.hash .y6) -
        DigitAdaptor.fromBits (raw.hash .x7) := by
  simp only [Coordinates.table, CurveMembership.garble, secretOracles, bitsK_secretWindows]

/-- Every row of the reference table is the pad secret masked with the slope and hash. -/
theorem Coordinates.table_rows (bridgeKey : BaseField) (key : InputMacKey) (raw : Coordinates)
    (adaptor : CurveAdaptor) (index : Fin coordinateBitCount) :
    (tableRows (raw.table bridgeKey key) adaptor).get index =
      ⟨raw.pad adaptor index ^^^ BitAdaptor.fieldBytes (raw.slope adaptor + raw.hash adaptor index)⟩ := by
  cases adaptor <;>
    simp only [Coordinates.table, CurveMembership.garble, secretOracles, bitsK_secretWindows,
      tableRows, garble_secretWindows_row, Coordinates.slope, slopeOf]

/-! ### The middle coordinates of one input -/

/-- The coordinate bits each adaptor family reads. -/
def inputBits (input : AffineInput) : CurveAdaptor → Fin coordinateBitCount → Bool
  | .y4 => coordinateValues input.y
  | .y6 => coordinateValues input.y
  | .x3 => coordinateValues input.x
  | .x5 => coordinateValues input.x
  | .x7 => coordinateValues input.x

/-- The selected output of each gate: the slope is added where the bit is set. -/
def selectOutput (bits : Fin coordinateBitCount → Bool) (slope : BaseField)
    (hash : Fin coordinateBitCount → BaseField) : Fin coordinateBitCount → BaseField :=
  fun index => if bits index then slope + hash index else hash index

/-- The hash secret recovered from the selected output. -/
def unselectOutput (bits : Fin coordinateBitCount → Bool) (slope : BaseField)
    (output : Fin coordinateBitCount → BaseField) : Fin coordinateBitCount → BaseField :=
  fun index => if bits index then output index - slope else output index

theorem unselectOutput_selectOutput (bits : Fin coordinateBitCount → Bool) (slope : BaseField)
    (hash : Fin coordinateBitCount → BaseField) :
    unselectOutput bits slope (selectOutput bits slope hash) = hash := by
  funext index
  simp only [unselectOutput, selectOutput]
  split <;> ring

theorem selectOutput_unselectOutput (bits : Fin coordinateBitCount → Bool) (slope : BaseField)
    (output : Fin coordinateBitCount → BaseField) :
    selectOutput bits slope (unselectOutput bits slope output) = output := by
  funext index
  simp only [unselectOutput, selectOutput]
  split <;> ring

/-- Raw coordinates to middle coordinates: `(mask, c1, c2, selected outputs, rows)`. -/
def encodeCoordinates (input : AffineInput) (raw : Coordinates) : Coordinates where
  mask := raw.mask
  r1 := raw.mask + raw.r1
  r2 := -raw.mask + raw.r2
  hash := fun adaptor =>
    selectOutput (inputBits input adaptor) (raw.slope adaptor) (raw.hash adaptor)
  pad := fun adaptor index =>
    raw.pad adaptor index ^^^ BitAdaptor.fieldBytes (raw.slope adaptor + raw.hash adaptor index)

/-- The hash secrets recovered from the selected outputs, adaptor by adaptor. -/
def decodeY4 (input : AffineInput) (r2 : BaseField) (output : GateValues BaseField) :
    Fin coordinateBitCount → BaseField :=
  unselectOutput (inputBits input .y4) (-r2) (output .y4)

def decodeY6 (input : AffineInput) (r2 : BaseField) (output : GateValues BaseField) :
    Fin coordinateBitCount → BaseField :=
  unselectOutput (inputBits input .y6) (-DigitAdaptor.fromBits (decodeY4 input r2 output))
    (output .y6)

def decodeX3 (input : AffineInput) (r1 : BaseField) (output : GateValues BaseField) :
    Fin coordinateBitCount → BaseField :=
  unselectOutput (inputBits input .x3) (-r1) (output .x3)

def decodeX5 (input : AffineInput) (r1 : BaseField) (output : GateValues BaseField) :
    Fin coordinateBitCount → BaseField :=
  unselectOutput (inputBits input .x5) (-DigitAdaptor.fromBits (decodeX3 input r1 output))
    (output .x5)

def decodeX7 (input : AffineInput) (r1 : BaseField) (output : GateValues BaseField) :
    Fin coordinateBitCount → BaseField :=
  unselectOutput (inputBits input .x7) (-DigitAdaptor.fromBits (decodeX5 input r1 output))
    (output .x7)

def decodeHash (input : AffineInput) (r1 r2 : BaseField) (output : GateValues BaseField) :
    GateValues BaseField
  | .y4 => decodeY4 input r2 output
  | .y6 => decodeY6 input r2 output
  | .x3 => decodeX3 input r1 output
  | .x5 => decodeX5 input r1 output
  | .x7 => decodeX7 input r1 output

/-- Middle coordinates to raw coordinates. -/
def decodeCoordinates (input : AffineInput) (middle : Coordinates) : Coordinates :=
  let hash := decodeHash input (middle.r1 - middle.mask) (middle.r2 + middle.mask) middle.hash
  let slope := slopeOf (middle.r1 - middle.mask) (middle.r2 + middle.mask) hash
  { mask := middle.mask
    r1 := middle.r1 - middle.mask
    r2 := middle.r2 + middle.mask
    hash
    pad := fun adaptor index =>
      middle.pad adaptor index ^^^ BitAdaptor.fieldBytes (slope adaptor + hash adaptor index) }

theorem decodeHash_encodeCoordinates (input : AffineInput) (raw : Coordinates) :
    decodeHash input raw.r1 raw.r2 (encodeCoordinates input raw).hash = raw.hash := by
  have y4 : decodeY4 input raw.r2 (encodeCoordinates input raw).hash = raw.hash .y4 :=
    unselectOutput_selectOutput _ _ _
  have y6 : decodeY6 input raw.r2 (encodeCoordinates input raw).hash = raw.hash .y6 := by
    unfold decodeY6
    rw [y4]
    exact unselectOutput_selectOutput _ _ _
  have x3 : decodeX3 input raw.r1 (encodeCoordinates input raw).hash = raw.hash .x3 :=
    unselectOutput_selectOutput _ _ _
  have x5 : decodeX5 input raw.r1 (encodeCoordinates input raw).hash = raw.hash .x5 := by
    unfold decodeX5
    rw [x3]
    exact unselectOutput_selectOutput _ _ _
  have x7 : decodeX7 input raw.r1 (encodeCoordinates input raw).hash = raw.hash .x7 := by
    unfold decodeX7
    rw [x5]
    exact unselectOutput_selectOutput _ _ _
  funext adaptor
  cases adaptor
  · exact y4
  · exact y6
  · exact x3
  · exact x5
  · exact x7

theorem selectOutput_decodeHash (input : AffineInput) (r1 r2 : BaseField)
    (output : GateValues BaseField) (adaptor : CurveAdaptor) :
    selectOutput (inputBits input adaptor) (slopeOf r1 r2 (decodeHash input r1 r2 output) adaptor)
      (decodeHash input r1 r2 output adaptor) = output adaptor := by
  cases adaptor <;> exact selectOutput_unselectOutput _ _ _

theorem decodeCoordinates_encodeCoordinates (input : AffineInput) (raw : Coordinates) :
    decodeCoordinates input (encodeCoordinates input raw) = raw := by
  obtain ⟨mask, r1, r2, hash, pad⟩ := raw
  have r1Eq : (encodeCoordinates input ⟨mask, r1, r2, hash, pad⟩).r1 -
      (encodeCoordinates input ⟨mask, r1, r2, hash, pad⟩).mask = r1 :=
    add_sub_cancel_left mask r1
  have r2Eq : (encodeCoordinates input ⟨mask, r1, r2, hash, pad⟩).r2 +
      (encodeCoordinates input ⟨mask, r1, r2, hash, pad⟩).mask = r2 :=
    neg_add_cancel_comm mask r2
  have hashEq := decodeHash_encodeCoordinates input ⟨mask, r1, r2, hash, pad⟩
  unfold decodeCoordinates
  simp only [r1Eq, r2Eq, hashEq]
  refine Coordinates.ext rfl rfl rfl rfl ?_
  funext adaptor index
  exact xor_xor_cancel _ _

theorem encodeCoordinates_decodeCoordinates (input : AffineInput) (middle : Coordinates) :
    encodeCoordinates input (decodeCoordinates input middle) = middle := by
  obtain ⟨c0, c1, c2, output, rows⟩ := middle
  refine Coordinates.ext rfl (add_sub_cancel c0 c1) (show -c0 + (c2 + c0) = c2 by ring) ?_ ?_
  · funext adaptor
    exact selectOutput_decodeHash input _ _ output adaptor
  · funext adaptor index
    exact xor_xor_cancel _ _

/-- For one input, raw coordinates and middle coordinates are in bijection. -/
def middleEquiv (input : AffineInput) : Coordinates ≃ Coordinates where
  toFun := encodeCoordinates input
  invFun := decodeCoordinates input
  left_inv := decodeCoordinates_encodeCoordinates input
  right_inv := encodeCoordinates_decodeCoordinates input

end Kriterion.ArgoMAC.Security
