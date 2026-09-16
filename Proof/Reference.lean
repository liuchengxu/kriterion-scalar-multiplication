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

/-- The slope of each adaptor family in the reference table. -/
def Coordinates.slope (raw : Coordinates) : CurveAdaptor → BaseField
  | .y4 => -raw.r2
  | .y6 => -DigitAdaptor.fromBits (raw.hash .y4)
  | .x3 => -raw.r1
  | .x5 => -DigitAdaptor.fromBits (raw.hash .x3)
  | .x7 => -DigitAdaptor.fromBits (raw.hash .x5)

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
      tableRows, garble_secretWindows_row, Coordinates.slope]

end Kriterion.ArgoMAC.Security
