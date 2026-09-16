/-
This file proves the reparametrisation that removes an *intermediate*
programming of one fixed-key permutation.

The simulated side programs the steering gate twice: the reference-shaped
honest programming sends the selected label to the gate's own fiber chunk, and
then the steering sends the same label to the chunk it wants. The reference
game programs it once. The two views therefore differ, and the difference is
not a difference of the *final* view alone -- it is the composite

  `programmed (programmed permutation label first) label second`  versus
  `programmed permutation label second`.

The two are reparametrisations of one another. Programming at a label erases
the old image of that label, and the erased image is recoverable from the
programmed permutation only together with a free block: the map

  `permutation ↦ (programmed permutation label range, permutation label)`

is a bijection onto the permutations that send `label` to `range` times the
whole block space. So a uniform permutation, read through one programming,
is the same law as that programming together with an *independent uniform*
erased image (`uniform_programmed_erased`), and the intermediate programming
may be dropped from the programmed permutation itself
(`uniform_programmed_retarget`).

Both facts are proved by an explicit involution of the permutation space:
`shiftErased` moves the erased image by a fixed exclusive-or, and `retarget`
moves the intermediate range. Neither needs the ranges to be uniform, which is
what makes them usable after the digest secrets have already been replaced by
fiber samples.
-/

import Proof.Hidden

namespace Kriterion.ArgoMAC.Security

open Cryptography

/-! ### The algebra of one programming -/

/-- A programmed permutation sends the label to the requested range. -/
theorem programmed_apply_label (permutation : Equiv Block Block) (label range : Block) :
    programmed permutation label range label = range := by
  rw [programmed, Equiv.trans_apply, Equiv.swap_apply_left]

/-- Programming back to the erased image undoes the programming. -/
theorem programmed_programmed_label (permutation : Equiv Block Block) (label range : Block) :
    programmed (programmed permutation label range) label (permutation label) = permutation :=
  congrArg Prod.fst (programAt_programAt label (permutation, range))

/-! ### Moving the erased image -/

/-- The permutation whose programming at `label` to `range` is the same, but whose erased
image of `label` is moved by `shift`. -/
def shiftErased (label range shift : Block) (permutation : Equiv Block Block) :
    Equiv Block Block :=
  programmed (programmed permutation label range) label (permutation label ^^^ shift)

theorem shiftErased_apply_label (label range shift : Block) (permutation : Equiv Block Block) :
    shiftErased label range shift permutation label = permutation label ^^^ shift :=
  programmed_apply_label _ _ _

theorem programmed_shiftErased (label range shift : Block) (permutation : Equiv Block Block) :
    programmed (shiftErased label range shift permutation) label range =
      programmed permutation label range := by
  have base := programmed_programmed_label (programmed permutation label range) label
    (permutation label ^^^ shift)
  rw [programmed_apply_label] at base
  exact base

theorem shiftErased_shiftErased (label range shift : Block) (permutation : Equiv Block Block) :
    shiftErased label range shift (shiftErased label range shift permutation) = permutation := by
  show programmed (programmed (shiftErased label range shift permutation) label range) label
      (shiftErased label range shift permutation label ^^^ shift) = permutation
  rw [programmed_shiftErased, shiftErased_apply_label, xor_xor_cancel,
    programmed_programmed_label]

/-- Moving the erased image is an involution of the permutation space. -/
def shiftErasedEquiv (label range shift : Block) : Equiv Block Block ≃ Equiv Block Block where
  toFun := shiftErased label range shift
  invFun := shiftErased label range shift
  left_inv := shiftErased_shiftErased label range shift
  right_inv := shiftErased_shiftErased label range shift

/-! ### Moving the intermediate range -/

/-- The permutation whose double programming through `first` is the double programming of
this one through `second`, with the same erased image. -/
def retarget (label first second : Block) (permutation : Equiv Block Block) :
    Equiv Block Block :=
  programmed (programmed (programmed permutation label first) label second) label
    (permutation label)

theorem retarget_apply_label (label first second : Block) (permutation : Equiv Block Block) :
    retarget label first second permutation label = permutation label :=
  programmed_apply_label _ _ _

theorem programmed_retarget (label first second : Block) (permutation : Equiv Block Block) :
    programmed (retarget label first second permutation) label second =
      programmed (programmed permutation label first) label second := by
  have base := programmed_programmed_label
    (programmed (programmed permutation label first) label second) label (permutation label)
  rw [programmed_apply_label] at base
  exact base

theorem retarget_retarget (label first second : Block) (permutation : Equiv Block Block) :
    retarget label second first (retarget label first second permutation) = permutation := by
  have inner := programmed_programmed_label (programmed permutation label first) label second
  rw [programmed_apply_label] at inner
  show programmed (programmed (programmed (retarget label first second permutation) label second)
      label first) label (retarget label first second permutation label) = permutation
  rw [programmed_retarget, retarget_apply_label, inner, programmed_programmed_label]

/-- Moving the intermediate range is a bijection of the permutation space. -/
def retargetEquiv (label first second : Block) : Equiv Block Block ≃ Equiv Block Block where
  toFun := retarget label first second
  invFun := retarget label second first
  left_inv := retarget_retarget label first second
  right_inv := retarget_retarget label second first

/-! ### Exclusive-or of blocks -/

/-- Exclusive-or with a fixed block is an involution. -/
def xorBlock (value : Block) : Block ≃ Block where
  toFun other := value ^^^ other
  invFun other := value ^^^ other
  left_inv other := by
    show value ^^^ (value ^^^ other) = other
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  right_inv other := by
    show value ^^^ (value ^^^ other) = other
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

noncomputable section

theorem uniform_block_xor {Result : Type} (value : Block)
    (continuation : Block → PMF Result) :
    ((PMF.uniformOfFintype Block).bind fun other => continuation (value ^^^ other)) =
      (PMF.uniformOfFintype Block).bind continuation :=
  uniformOfFintype_bind_equiv (xorBlock value) continuation

/-! ### The two reparametrisation laws -/

/-- Moving the erased image by a fixed exclusive-or does not change the game. -/
theorem uniform_programmed_shift {Result : Type} (label range shift : Block)
    (continuation : Equiv Block Block → Block → PMF Result) :
    ((PMF.uniformOfFintype (Equiv Block Block)).bind fun permutation =>
        continuation (programmed permutation label range) (permutation label)) =
      (PMF.uniformOfFintype (Equiv Block Block)).bind fun permutation =>
        continuation (programmed permutation label range) (permutation label ^^^ shift) := by
  have base := uniformOfFintype_bind_equiv (shiftErasedEquiv label range shift)
    fun permutation => continuation (programmed permutation label range) (permutation label)
  refine base.symm.trans (congrArg (PMF.bind _) (funext fun permutation => ?_))
  show continuation (programmed (shiftErased label range shift permutation) label range)
      (shiftErased label range shift permutation label) =
    continuation (programmed permutation label range) (permutation label ^^^ shift)
  rw [programmed_shiftErased, shiftErased_apply_label]

/-- A uniform permutation read through one programming is that programming together with an
independent uniform erased image. This is the reparametrisation that removes the
intermediate programming of the steering gate: the erased image is free. -/
theorem uniform_programmed_erased {Result : Type} (label range : Block)
    (continuation : Equiv Block Block → Block → PMF Result) :
    ((PMF.uniformOfFintype (Equiv Block Block)).bind fun permutation =>
        continuation (programmed permutation label range) (permutation label)) =
      (PMF.uniformOfFintype (Equiv Block Block)).bind fun permutation =>
        (PMF.uniformOfFintype Block).bind fun erased =>
          continuation (programmed permutation label range) erased := by
  have shifted : ((PMF.uniformOfFintype Block).bind fun shift =>
        (PMF.uniformOfFintype (Equiv Block Block)).bind fun permutation =>
          continuation (programmed permutation label range) (permutation label)) =
      (PMF.uniformOfFintype Block).bind fun shift =>
        (PMF.uniformOfFintype (Equiv Block Block)).bind fun permutation =>
          continuation (programmed permutation label range) (permutation label ^^^ shift) :=
    congrArg (PMF.bind _) (funext fun shift =>
      uniform_programmed_shift label range shift continuation)
  rw [PMF.bind_const] at shifted
  rw [shifted, PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun permutation => ?_)
  exact uniform_block_xor (permutation label) fun erased =>
    continuation (programmed permutation label range) erased

/-- The intermediate programming may be dropped: a uniform permutation programmed at a
label first to one range and then to another is, in law, the same permutation programmed
once to the second range. -/
theorem uniform_programmed_retarget {Result : Type} (label first second : Block)
    (continuation : Equiv Block Block → PMF Result) :
    ((PMF.uniformOfFintype (Equiv Block Block)).bind fun permutation =>
        continuation (programmed (programmed permutation label first) label second)) =
      (PMF.uniformOfFintype (Equiv Block Block)).bind fun permutation =>
        continuation (programmed permutation label second) := by
  have base := uniformOfFintype_bind_equiv (retargetEquiv label first second)
    fun permutation => continuation (programmed permutation label second)
  refine Eq.trans ?_ base
  refine congrArg (PMF.bind _) (funext fun permutation => ?_)
  exact congrArg continuation (programmed_retarget label first second permutation).symm

end

end Kriterion.ArgoMAC.Security
