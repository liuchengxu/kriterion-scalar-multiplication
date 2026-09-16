/-
This file bounds the mass of one 128-bit chunk of a hash-fiber sample.

The steering hop hides two programming ranges behind the adversary's log, and
each range is one 128-bit chunk of a 384-bit hash-fiber sample. To charge that
hop the chain needs the largest point mass of such a chunk.

A *fixed* target is the wrong place to look for it. The fiber of one field
element is the arithmetic progression `target + k * p` inside `2 ^ 384`, and the
number of its members whose middle chunk takes a prescribed value is an
equidistribution question about `p` modulo `2 ^ 256`, not something a counting
argument settles. The chain does not need it either: the target of the steering
gate's fiber sample is the gate's own selected output, which is uniform given
everything the adversary has seen. So the law to bound is the *marginal* one --
a uniform field element, then a uniform sample of its fiber -- and that law is
within `p / 2 ^ 384` of the uniform 384-bit law in total difference
(`hashFiber_total_difference`).

The uniform 384-bit law has an exactly uniform chunk, because a digest is its
three chunks (`digestChunkEquiv`). So the chunk of the marginal fiber sample has
every point mass at most `1 / 2 ^ 128 + p / 2 ^ 384 ≤ 2 / 2 ^ 128`, which is what
the steering hop's accounting charges for it.
-/

import Proof.Chain
import Proof.Product

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

set_option exponentiation.threshold 400

/-! ### A digest is its three chunks -/

/-- The three 128-bit chunks of a digest, the low chunk first. -/
def digestChunks (digest : BitVec 384) : Block × Block × Block :=
  (digest.extractLsb' 0 128, digest.extractLsb' 128 128, digest.extractLsb' 256 128)

/-- The digest rebuilt from its three chunks. -/
def joinChunks (chunks : Block × Block × Block) : BitVec 384 :=
  chunks.2.2 ++ (chunks.2.1 ++ chunks.1)

theorem joinChunks_digestChunks (digest : BitVec 384) :
    joinChunks (digestChunks digest) = digest := by
  show digest.extractLsb' 256 128 ++
    (digest.extractLsb' 128 128 ++ digest.extractLsb' 0 128) = digest
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by norm_num),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by norm_num)]
  exact BitVec.extractLsb'_eq_self

theorem digestChunks_injective : Function.Injective digestChunks := by
  intro first second equal
  rw [← joinChunks_digestChunks first, ← joinChunks_digestChunks second, equal]

theorem card_block : Fintype.card Block = 2 ^ 128 :=
  (Fintype.card_congr
    (BitVec.equivFin : BitVec 128 ≃+* Fin (2 ^ 128)).toEquiv).trans (Fintype.card_fin _)

theorem card_bitVec_384_eq_chunks :
    Fintype.card (BitVec 384) = Fintype.card (Block × Block × Block) := by
  rw [card_bitVec_384, Fintype.card_prod, Fintype.card_prod, card_block, ← pow_add, ← pow_add]

/-- A digest and its three chunks are in bijection. -/
def digestChunkEquiv : BitVec 384 ≃ Block × Block × Block :=
  Equiv.ofBijective digestChunks
    ((Fintype.bijective_iff_injective_and_card digestChunks).mpr
      ⟨digestChunks_injective, card_bitVec_384_eq_chunks⟩)

theorem map_uniform_digestChunks :
    (PMF.uniformOfFintype (BitVec 384)).map digestChunks =
      PMF.uniformOfFintype (Block × Block × Block) :=
  uniformOfFintype_map_bijection digestChunkEquiv

/-! ### The marginals of a uniform pair -/

theorem uniformOfFintype_map_fst {Left Right : Type} [Fintype Left] [Nonempty Left]
    [Fintype Right] [Nonempty Right] :
    (PMF.uniformOfFintype (Left × Right)).map Prod.fst = PMF.uniformOfFintype Left := by
  have base := uniformOfFintype_bind_prod (fun (left : Left) (_ : Right) => PMF.pure left)
  simp only [PMF.bind_const, PMF.bind_pure] at base
  exact base.symm

theorem uniformOfFintype_map_snd {Left Right : Type} [Fintype Left] [Nonempty Left]
    [Fintype Right] [Nonempty Right] :
    (PMF.uniformOfFintype (Left × Right)).map Prod.snd = PMF.uniformOfFintype Right := by
  have base := uniformOfFintype_bind_prod (fun (_ : Left) (right : Right) => PMF.pure right)
  simp only [PMF.bind_pure, PMF.bind_const] at base
  exact base.symm

/-! ### The chunk of a uniform digest is a uniform block -/

/-- Every chunk of a uniform digest is a uniform block. -/
theorem map_uniformDigest_chunk (offset : Nat)
    (valid : offset = 0 ∨ offset = 128 ∨ offset = 256) :
    (PMF.uniformOfFintype (BitVec 384)).map
        (fun digest => digest.extractLsb' offset 128) = PMF.uniformOfFintype Block := by
  rcases valid with rfl | rfl | rfl
  · rw [show (fun digest : BitVec 384 => digest.extractLsb' 0 128) =
        Prod.fst ∘ digestChunks from rfl, ← PMF.map_comp, map_uniform_digestChunks]
    exact uniformOfFintype_map_fst
  · rw [show (fun digest : BitVec 384 => digest.extractLsb' 128 128) =
        (Prod.fst ∘ Prod.snd) ∘ digestChunks from rfl, ← PMF.map_comp, map_uniform_digestChunks,
      ← PMF.map_comp, uniformOfFintype_map_snd]
    exact uniformOfFintype_map_fst
  · rw [show (fun digest : BitVec 384 => digest.extractLsb' 256 128) =
        (Prod.snd ∘ Prod.snd) ∘ digestChunks from rfl, ← PMF.map_comp, map_uniform_digestChunks,
      ← PMF.map_comp, uniformOfFintype_map_snd]
    exact uniformOfFintype_map_snd

/-- One chunk value of a uniform digest has mass exactly `1 / 2 ^ 128`. -/
theorem uniformDigest_chunk_apply (offset : Nat)
    (valid : offset = 0 ∨ offset = 128 ∨ offset = 256) (value : Block) :
    (((PMF.uniformOfFintype (BitVec 384)).map
        fun digest => digest.extractLsb' offset 128) value).toReal = 1 / 2 ^ 128 := by
  rw [map_uniformDigest_chunk offset valid, PMF.uniformOfFintype_apply, card_block,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div, Nat.cast_pow, Nat.cast_ofNat]

/-! ### The chunk of a hash-fiber sample -/

/-- A chunk of a hash-fiber sample taken at a uniform target has every point mass at most
`2 / 2 ^ 128`.

This is the honest replacement for a fixed-target chunk bound: the steering gate's fiber
target is its own selected output, which the released table leaves uniform, so the law that
has to be bounded is the marginal one. -/
theorem fiberChunk_mass_le (offset : Nat)
    (valid : offset = 0 ∨ offset = 128 ∨ offset = 256) (value : Block) :
    (((((PMF.uniformOfFintype BaseField).bind uniformHashFiber).map
        fun digest => digest.extractLsb' offset 128)) value).toReal ≤ 2 / 2 ^ 128 := by
  have chunkBind : ∀ law : PMF (BitVec 384),
      (law.bind fun digest => PMF.pure (digest.extractLsb' offset 128)) =
        law.map fun digest => digest.extractLsb' offset 128 := fun _ => rfl
  have difference := bind_apply_sub_le ((PMF.uniformOfFintype BaseField).bind uniformHashFiber)
    (PMF.uniformOfFintype (BitVec 384))
    (fun digest => PMF.pure (digest.extractLsb' offset 128)) value
  rw [chunkBind, chunkBind, uniformDigest_chunk_apply offset valid value] at difference
  have total := hashFiber_total_difference
  have modulusLe : (baseFieldModulus : ℝ) / 2 ^ 384 ≤ 1 / 2 ^ 128 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc (baseFieldModulus : ℝ) * 2 ^ 128 ≤ 2 ^ 254 * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right baseFieldModulus_le (by positivity)
      _ ≤ 1 * 2 ^ 384 := by rw [one_mul, ← pow_add]; norm_num
  have bound := abs_le.mp (difference.trans (total.trans modulusLe))
  have twice : (1 : ℝ) / 2 ^ 128 + 1 / 2 ^ 128 = 2 / 2 ^ 128 := by ring
  linarith [bound.2]

end

end Kriterion.ArgoMAC.Security
