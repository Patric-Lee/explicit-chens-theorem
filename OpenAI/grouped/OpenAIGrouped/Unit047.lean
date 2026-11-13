import OpenAIGrouped.Unit046
import OpenAIGrouped.Unit020
import OpenAIGrouped.Unit021
import OpenAIGrouped.Unit014
import OpenAIGrouped.Unit022
import OpenAIGrouped.Unit024
import OpenAIGrouped.Unit018
import OpenAIGrouped.Unit033
import OpenAIGrouped.Unit016
import OpenAIGrouped.Unit010
import OpenAIGrouped.Unit015
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit019

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Energy/Reindex.lean; sha256: 25310975852db2f8766251fc321f54ec2093dffb9e22ffabf12b37053cb27fdc -/
section Source1880
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyReindex
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O

variable {α β:Type*}[Fintype α][Fintype β]

lemma positive_reindex (e:α≃β)(η:Character)(m A z:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ (pool∘e) (coeff∘e) (P∘e) t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ pool coeff P t X₁ X₂:=by
  unfold positiveSlotRow
  simp only [Function.comp_apply,e.prod_comp P,
    e.prod_comp (fun i=>CenteredMomentHeckeSlots.rowSlot η m A z (pool i) (coeff i) t)]

theorem energy_reindex (e:α≃β)(η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (pool∘e) (coeff∘e) (P∘e) X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_reindex]

omit [Fintype α] [Fintype β] in
theorem energy_subset_map (e:α↪β)(T:Finset α)(η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (fun i:T=>pool (e i)) (fun i:T=>coeff (e i))
      (fun i:T=>P (e i)) X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i:T.map e=>pool i) (fun i:T.map e=>coeff i)
      (fun i:T.map e=>P i) X₁ X₂ keep Φ K:=
  energy_reindex (Finset.equivMap e T) η m A W₁ W₂
    (fun i:T.map e=>pool i) (fun i:T.map e=>coeff i) (fun i:T.map e=>P i)
    t X₁ X₂ keep Φ K

end SevenEighths.CenteredMomentEnergyReindex

end

end OAI

end Source1880

/- Original source: OAI/NumberTheory/DirichletL/Moments/SlotClassTransport.lean; sha256: 577d14af36cd608c2a0d8b7bcdfd6e90551dff74436bd082802de67e07907a33 -/
section Source1881
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentSlotClassTransport
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentAllocatedNaturalSource CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentRetainedEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem common_fixed_slot_coefficient (s : Input ι) (ν : ι→Character)
    (hν : ∀i I,s.ν i I=idealCoeff (ν i) I)
    (τ : Character) (v : ℝ) (C R : Ideal O) (B : actualAllocations s.pools C)
    (i : CenteredMomentCommonProfile.liveIndices B.val) (I : Ideal O) :
    (commonData (withHeight s τ v) C R B).coefficient i I=
      idealCoeff (ν i.val) I*s.W i.val ((I.absNorm:ℝ)/s.P i.val) := by
  change s.ν i.val I*s.W i.val ((I.absNorm:ℝ)/s.P i.val)=_
  rw [hν]

omit [DecidableEq ι] in
theorem commonSlots_fixed_coefficient (s : Input ι) (ν : ι→Character)
    (hν : ∀i I,s.ν i I=idealCoeff (ν i) I)
    (τ : Character) (v : ℝ) (C : Ideal O) (B : actualAllocations s.pools C)
    (i : CenteredMomentCommonProfile.liveIndices B.val) (I : Ideal O) :
    (commonSlots (withHeight s τ v) C B).coefficient i I=
      idealCoeff (ν i.val) I*s.W i.val ((I.absNorm:ℝ)/s.P i.val) := by
  change s.ν i.val I*s.W i.val ((I.absNorm:ℝ)/s.P i.val)=_
  rw [hν]

theorem allocated_fixed_character_gate (s : Input ι) (ν : ι→Character)
    (Q : Ideal O) (hQ : ∀i,Q≤(ν i).modulus)
    (τ : Character) (v : ℝ) (C R L : Ideal O) (B : actualAllocations s.pools C)
    (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2)))
    (i : CenteredMomentDivisorRaw.liveIndices L a) :
    Q≤(ν i.val.val).modulus ∧
    (commonData (withHeight s τ v) C R B).slots i.val=s.slots i.val.val ∧
    (commonData (withHeight s τ v) C R B).P i.val=s.P i.val.val ∧
    (commonData (withHeight s τ v) C R B).W i.val=s.W i.val.val :=
  ⟨hQ _,rfl,rfl,rfl⟩

theorem allocated_positive_fixed_characters (s : Input ι) (ν : ι→Character)
    (hν : ∀i I,s.ν i I=idealCoeff (ν i) I)
    (τ : Character) (v : ℝ) (C R L : Ideal O) (B : actualAllocations s.pools C)
    (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2)))
    (z : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ) :
    let d:=commonData (withHeight s τ v) C R B
    allocatedPositiveRow d.η d.m d.A z d.t d.slots d.coefficient d.P L a W₁ W₂ X₁ X₂=
      retainedPositiveRow τ
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator (R*C))
        1 z W₁ W₂
        (fun i : CenteredMomentDivisorRaw.liveIndices L a=>s.slots i.val.val)
        (fun i : CenteredMomentDivisorRaw.liveIndices L a=>fun I=>
          idealCoeff (ν i.val.val) I*s.W i.val.val ((I.absNorm:ℝ)/s.P i.val.val))
        (fun i : CenteredMomentDivisorRaw.liveIndices L a=>s.P i.val.val) v
        (X₁/Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain L a 0))
        (X₂/Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain L a 1)) := by
  dsimp only
  unfold allocatedPositiveRow
  have he : (fun i : CenteredMomentDivisorRaw.liveIndices L a=>
      (commonData (withHeight s τ v) C R B).coefficient i.val)=
    (fun i : CenteredMomentDivisorRaw.liveIndices L a=>fun I=>
      idealCoeff (ν i.val.val) I*s.W i.val.val ((I.absNorm:ℝ)/s.P i.val.val)) := by
    funext i I
    exact common_fixed_slot_coefficient s ν hν τ v C R B i.val I
  rw [he]
  rfl

end SevenEighths.CenteredMomentSlotClassTransport

end

end OAI

end Source1881

/- Original source: OAI/NumberTheory/DirichletL/Moments/AllocatedRayDictionary.lean; sha256: 85c40e5529aa469a9cc99037fcbc89c630b88a1fd6181e56636795d391a45e48 -/
section Source1882
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentAllocatedRayDictionary
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeCancellation
local notation "O" => HeckeFamily.O

variable {α : Type*} [Fintype α] [DecidableEq α]

def originalEmbedding (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C) :
    CenteredMomentCommonProfile.liveIndices B.val ↪ α :=
  ⟨Subtype.val, Subtype.val_injective⟩

def remaining (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    Finset (CenteredMomentCommonProfile.liveIndices B.val) :=
  CenteredMomentDivisorRaw.liveIndices (ι := CenteredMomentCommonProfile.liveIndices B.val) L a \ J

def originalImage (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) : Finset α :=
  (remaining s C B L a J).map (originalEmbedding s C B)

lemma projection_injective (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    Function.Injective (fun i : remaining s C B L a J => i.val.val) := by
  intro i j h
  exact Subtype.ext (Subtype.ext h)

lemma mem_originalImage (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) (i : α) :
    i ∈ originalImage s C B L a J ↔
      ∃ j ∈ remaining s C B L a J, j.val = i := by
  simp only [originalImage, Finset.mem_map, originalEmbedding, Function.Embedding.coeFn_mk]

lemma originalImage_card (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    (originalImage s C B L a J).card = (remaining s C B L a J).card := Finset.card_map _

def commonFirst (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : ℝ :=
  if left then (commonData s C R B).X₁ else (commonData s C R B).Y₁

def commonSecond (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : ℝ :=
  if left then (commonData s C R B).X₂ else (commonData s C R B).Y₂

omit [DecidableEq α] in
lemma commonFirst_pos (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : 0 < commonFirst s C R B left := by
  unfold commonFirst
  split
  · exact (commonData s C R B).X₁_pos
  · exact (commonData s C R B).Y₁_pos

omit [DecidableEq α] in
lemma commonSecond_pos (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : 0 < commonSecond s C R B left := by
  unfold commonSecond
  split
  · exact (commonData s C R B).X₂_pos
  · exact (commonData s C R B).Y₂_pos

section RayData
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

structure Matches (s : Input α) (η₀ : Character)
    (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
    (W : ℝ → ℂ) (bslot Z : ℝ) : Prop where
  character : ∀ i I, s.ν i I = idealCoeff (relativeCharacter M H hH η₀ (θ i)) I
  profile : ∀ i y, s.W i y = W y * (y : ℂ)^(-HeckeDyadic.shift (σ i) (freq i))
  pool : ∀ i, s.slots i = primePool M H bslot (Z^(w i))
  scale : ∀ i, s.P i = Z^(w i)

variable {M H hH}
variable {s : Input α} {η₀ : Character} {θ : α → RayQuotient.Characters M H}
  {w σ freq : α → ℝ} {W : ℝ → ℂ} {bslot Z : ℝ}
  (h : Matches M H hH s η₀ θ w σ freq W bslot Z)

include h

omit [DecidableEq α] in
lemma common_coefficient (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (i : CenteredMomentCommonProfile.liveIndices B.val)
    (I : Ideal O) :
    (commonData (withHeight s τ v) C R B).coefficient i I =
      idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
        annularWeight W (Z^(w i.val)) (σ i.val) (freq i.val) I := by
  change s.ν i.val I * s.W i.val ((I.absNorm : ℝ) / s.P i.val) = _
  rw [h.character, h.profile, h.scale]
  rfl

omit [DecidableEq α] in
lemma common_height_coefficient (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (i : CenteredMomentCommonProfile.liveIndices B.val)
    (I : Ideal O) (hI : I ≠ 0) :
    heightCoefficient ((commonData (withHeight s τ v) C R B).coefficient i) v I =
      ((Z^(w i.val) : ℝ) : ℂ)^(Complex.I*v) *
        (idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
          annularWeight W (Z^(w i.val)) (σ i.val) (v+freq i.val) I) := by
  have he : (commonData (withHeight s τ v) C R B).coefficient i =
      fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
        annularWeight W (Z^(w i.val)) (σ i.val) (freq i.val) I :=
    funext (common_coefficient h τ v C R B i)
  rw [he]
  exact CenteredMomentEnergySlotHeight.height_coefficient _ W _ _ _ v
    (h.scale i.val ▸ s.P_pos i.val) I hI

omit [DecidableEq α] in
lemma scale_phase_norm (i : α) (v : ℝ) :
    ‖((Z^(w i) : ℝ) : ℂ)^(Complex.I*v)‖ = 1 := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos (h.scale i ▸ s.P_pos i) (Complex.I*v)

theorem common_energy (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (m A : O) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d := commonData (withHeight s τ v) C R B
    energy τ m A 0 W₁ W₂
      (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) X₁ X₂ keep Φ K =
    energy τ m A 0 W₁ W₂
      (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) X₁ X₂ keep Φ K := by
  dsimp only
  have hc : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).coefficient i.val) =
      fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i.val.val)) I *
        annularWeight W (Z^(w i.val.val)) (σ i.val.val) (freq i.val.val) I := by
    funext i I
    exact common_coefficient h τ v C R B i.val I
  have hp : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).P i.val) = fun i => Z^(w i.val.val) := by
    funext i
    exact h.scale i.val.val
  have hs : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).slots i.val) =
      fun i => primePool M H bslot (Z^(w i.val.val)) := by
    funext i
    exact h.pool i.val.val
  have hhc := congrArg (fun f => fun i : remaining s C B L a J => heightCoefficient (f i) v) hc
  rw [hhc, hp, hs]
  rw [CenteredMomentEnergySlotHeight.inherited_height_energy τ m A W₁ W₂ _ _ _ _ _ _
    (fun i => h.scale i.val.val ▸ s.P_pos i.val.val)
    (fun i I hI => (s.prime i.val.val I (by rw [h.pool]; exact hI)).ne_zero)
    v 0 X₁ X₂ keep Φ K]
  exact CenteredMomentEnergyReindex.energy_subset_map (originalEmbedding s C B)
    (remaining s C B L a J) τ m A W₁ W₂
    (fun i => primePool M H bslot (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
    (fun i => Z^(w i)) 0 X₁ X₂ keep Φ K

theorem common_clipped_energy (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (V₁ V₂ : Plain) (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (D₁ D₂ : Finset (Ideal O)) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d := commonData (withHeight s τ v) C R B
    let W₁ := V₁.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ hX₁ 0) v
    let W₂ := V₂.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ hX₂ 1) v
    let Y₁ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)
    let Y₂ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
      W₁ W₂ (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) Y₁ Y₂ keep Φ K =
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
      W₁ W₂ (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) Y₁ Y₂ keep Φ K :=
  common_energy h τ v C R B L a J _ 1 _ _ _ _ keep Φ K

theorem both_common_rectangles (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (V₁ V₂ : Plain) (left : Bool)
    (D₁ D₂ : Finset (Ideal O)) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let X₁ := commonFirst s C R B left
    let X₂ := commonSecond s C R B left
    let hX₁ := commonFirst_pos s C R B left
    let hX₂ := commonSecond_pos s C R B left
    let d := commonData (withHeight s τ v) C R B
    let W₁ := V₁.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ hX₁ 0) v
    let W₂ := V₂.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ hX₂ 1) v
    let Y₁ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)
    let Y₂ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
      W₁ W₂ (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) Y₁ Y₂ keep Φ K =
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
      W₁ W₂ (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) Y₁ Y₂ keep Φ K :=
  common_clipped_energy h τ v C R B L a J V₁ V₂
    (commonFirst s C R B left) (commonSecond s C R B left)
    (commonFirst_pos s C R B left) (commonSecond_pos s C R B left) D₁ D₂ keep Φ K

omit h

lemma deleted_clipped_scale_pos (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (X : ℝ) (j : Fin 2) (D : Finset (Ideal O)) (hD : ∀I∈D,I≠0) :
    0 < clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X j)/(Ideal.absNorm (∏I∈D,I):ℝ) := by
  apply div_pos (zero_lt_one.trans_le (clippedScale_ge_one _))
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Finset.prod_ne_zero_iff.mpr hD))

lemma originalImage_fixedQ (Q : Ideal O) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus)
    (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (i : originalImage s C B L a J) :
    Q ≤ (relativeCharacter M H hH η₀ (θ i)).modulus :=
  relativeCharacter_fixedQ M H hH η₀ (θ i) Q hQM hQη

lemma originalImage_bounds (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (Lslot lo hi height heightShift v : ℝ)
    (hw : ∀i,0 ≤ w i) (hwL : ∀i,w i ≤ Lslot)
    (hσlo : ∀i,lo ≤ σ i) (hσhi : ∀i,σ i ≤ hi)
    (hf : ∀i,|freq i| ≤ height) (hv : |v| ≤ heightShift) :
    ∀i : originalImage s C B L a J,
      0 ≤ w i ∧ w i ≤ Lslot ∧ lo ≤ σ i ∧ σ i ≤ hi ∧ |v+freq i| ≤ height+heightShift := by
  intro i
  refine ⟨hw i, hwL i, hσlo i, hσhi i, ?_⟩
  exact (abs_add_le v (freq i)).trans (by linarith [hf i])

lemma originalImage_scale_bounds (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (hZ : 1<Z) (Lslot : ℝ) (hw : ∀i,0 ≤ w i) (hwL : ∀i,w i ≤ Lslot) :
    ∀i : originalImage s C B L a J, 1 ≤ Z^(w i) ∧ Z^(w i) ≤ Z^Lslot := by
  intro i
  exact ⟨Real.one_le_rpow hZ.le (hw i), Real.rpow_le_rpow_of_exponent_le hZ.le (hwL i)⟩

end RayData
end SevenEighths.CenteredMomentAllocatedRayDictionary

end

end OAI

end Source1882

/- Original source: OAI/NumberTheory/DirichletL/Energy/AmplifiedRayDictionary.lean; sha256: 81352bf6cd3904b6be633617d224fc8e5b6a1db395f499bcd6a342ad0ad753a2 -/
section Source1883
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary
open HeckeFamily CenteredMomentSecondHeightFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedRayDictionary
open CenteredMomentFirstAnnularInput CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentEligibleEnergy CenteredMomentCommonHeightEnvelope
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq β := Classical.decEq _

lemma active_pools_subset (s : Input α) (j : α⊕Fin 2) :
    (activeInput s).pools j⊆s.pools j := by
  cases j with
  | inl i => exact Finset.filter_subset _ _
  | inr j => exact Finset.Subset.refl _

lemma actualAllocations_mono {β : Type*} [Fintype β]
    (S T : β→Finset (Ideal O)) (h : ∀i,S i⊆T i) (C : Ideal O) :
    actualAllocations S C⊆actualAllocations T C := by
  intro B hB
  obtain ⟨hlabel,hprod⟩ := Finset.mem_filter.mp hB
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp hlabel
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v,?_,hvB⟩,hprod⟩
  exact Fintype.mem_piFinset.mpr (fun i=>h i (Fintype.mem_piFinset.mp hv i))

abbrev restoreAllocation (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : actualAllocations s.pools C :=
  ⟨B.val,actualAllocations_mono _ _ (active_pools_subset s) C B.property⟩

@[simp] lemma restoreAllocation_val (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : (restoreAllocation s C B).val=B.val := rfl

lemma restoreAllocation_injective (s : Input α) (C : Ideal O) :
    Function.Injective (restoreAllocation s C) := by
  intro B D h
  exact Subtype.ext (congrArg (fun x : actualAllocations s.pools C=>x.val) h)

lemma child_active (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (τ : Character) (t : ℝ) :
    child (activeInput s) C R B τ t=
      activeInput (child s C R (restoreAllocation s C B) τ t) := rfl

lemma active_coefficient (s : Input α) (i : α) :
    (activeInput s).toData.coefficient i=s.toData.coefficient i := rfl

lemma rowSlot_active (s : Input α) (i : α) (η : Character) (m A z : O) (t v : ℝ) :
    rowSlot η m A z ((activeInput s).slots i)
      (heightCoefficient ((activeInput s).toData.coefficient i) v) t=
    rowSlot η m A z (s.slots i) (heightCoefficient (s.toData.coefficient i) v) t := by
  unfold rowSlot
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro I hI hn
  have hz : s.W i ((I.absNorm:ℝ)/s.P i)=0 := by
    by_contra hh
    exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
  simp only [heightCoefficient,Data.coefficient,activeInput,hz,mul_zero,zero_mul]

lemma positive_active (s : Input α) (η : Character) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) :
    positiveSlotRow η m A z W₁ W₂ (activeInput s).slots
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient i) v)
      (activeInput s).P t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ s.slots
      (fun i=>heightCoefficient (s.toData.coefficient i) v) s.P t X₁ X₂ := by
  unfold positiveSlotRow
  congr 2
  exact Finset.prod_congr rfl (fun i _=>rowSlot_active s i η m A z t v)

theorem energy_active (s : Input α) (η : Character) (m A : O)
    (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ (activeInput s).slots
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient i) v)
      (activeInput s).P X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ s.slots
      (fun i=>heightCoefficient (s.toData.coefficient i) v) s.P X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_active]

theorem positive_active_restrict {κ : Type*} [Fintype κ] (s : Input α) (f : κ→α)
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) :
    positiveSlotRow η m A z W₁ W₂ (fun i=>(activeInput s).slots (f i))
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient (f i)) v)
      (fun i=>(activeInput s).P (f i)) t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ (fun i=>s.slots (f i))
      (fun i=>heightCoefficient (s.toData.coefficient (f i)) v)
      (fun i=>s.P (f i)) t X₁ X₂ := by
  unfold positiveSlotRow
  congr 2
  exact Finset.prod_congr rfl (fun i _=>rowSlot_active s (f i) η m A z t v)

theorem energy_active_restrict {κ : Type*} [Fintype κ] (s : Input α) (f : κ→α)
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ (fun i=>(activeInput s).slots (f i))
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient (f i)) v)
      (fun i=>(activeInput s).P (f i)) X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i=>s.slots (f i))
      (fun i=>heightCoefficient (s.toData.coefficient (f i)) v)
      (fun i=>s.P (f i)) X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_active_restrict]

theorem common_energy_active (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (τ : Character) (v : ℝ)
    (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)))
    (J : Finset (liveIndices B.val)) (m A : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d : CenteredMomentEligibleEnergy.Data (liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    let e : CenteredMomentEligibleEnergy.Data (liveIndices B.val) :=
      commonData (withHeight s τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools, restoreAllocation_val]
          using (restoreAllocation s C B).property⟩
    energy τ m A 0 W₁ W₂
      (fun i:remaining (activeInput s) C B L a J=>d.slots i.val)
      (fun i:remaining (activeInput s) C B L a J=>heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining (activeInput s) C B L a J=>d.P i.val) X₁ X₂ keep Φ K=
    energy τ m A 0 W₁ W₂
      (fun i:remaining s C (restoreAllocation s C B) L a J=>e.slots i.val)
      (fun i:remaining s C (restoreAllocation s C B) L a J=>heightCoefficient (e.coefficient i.val) v)
      (fun i:remaining s C (restoreAllocation s C B) L a J=>e.P i.val) X₁ X₂ keep Φ K := by
  exact energy_active_restrict s
    (fun i:remaining (activeInput s) C B L a J=>i.val.val) τ m A W₁ W₂ 0 v X₁ X₂ keep Φ K

def restoredError (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) : Input (liveIndices Bp.val) :=
  twiceChild s C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v

lemma error_source_active (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v=
      activeInput (restoredError s C R B τ t Q k Bp υ v) := rfl

theorem restoredError_data (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    let d:=restoredError s C R B τ t Q k Bp υ v
    d.η=υ ∧ d.t=v ∧ d.m=fixedBadMask*ConcretePrimeRowBridge.idealGenerator ((R*C)*(Q^k)) ∧
    d.X₁=s.X₁/(B.val (Sum.inr 0)).absNorm/(Bp.val (Sum.inr 0)).absNorm ∧
    d.X₂=s.X₂/(B.val (Sum.inr 1)).absNorm/(Bp.val (Sum.inr 1)).absNorm ∧
    d.Y₁=s.Y₁/(B.val (Sum.inr 0)).absNorm/(Bp.val (Sum.inr 0)).absNorm ∧
    d.Y₂=s.Y₂/(B.val (Sum.inr 1)).absNorm/(Bp.val (Sum.inr 1)).absNorm :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem error_live_slots (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)) :
    liveIndices Bp.val=Finset.univ :=
  prime_slots_live (activeInput (child s C R B τ t)) Q hQ k hslot Bp

theorem restoredError_volume (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    volume (restoredError s C R B τ t Q k Bp υ v)=
      volume s/(CenteredMomentCommonRawScale.rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  have hh:=child_volume (activeInput (child s C R B τ t)) Q hQ k hslot (R*C) Bp υ v
  rw [error_source_active,active_volume,active_volume,common_volume,div_div] at hh
  exact hh

theorem error_normalized_source (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    childNormalizedGaussSource (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp υ v Φ K=
      normalizedGaussSource (restoredError s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed Φ K := by
  unfold childNormalizedGaussSource
  rw [error_source_active,active_normalized]

theorem error_normalized_sum (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (υ : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)→Character)
    (v : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)→ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k),
      childNormalizedGaussSource (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp (υ Bp) (v Bp) Φ K)=
    ∑Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k),
      normalizedGaussSource (restoredError s C R B τ t Q k Bp (υ Bp) (v Bp)) ((R*C)*(Q^k)) seed Φ K :=
  Finset.sum_congr rfl (fun Bp _=>error_normalized_source s C R seed B τ t Q k Bp (υ Bp) (v Bp) Φ K)

theorem error_energy (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let e:=child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v
    let d:=restoredError s C R B τ t Q k Bp υ v
    energy e.η e.m 1 0 W₁ W₂ e.slots
      (fun i=>heightCoefficient (e.toData.coefficient i) e.t) e.P X₁ X₂ keep Φ K=
    energy d.η d.m 1 0 W₁ W₂ d.slots
      (fun i=>heightCoefficient (d.toData.coefficient i) d.t) d.P X₁ X₂ keep Φ K := by
  dsimp only
  rw [error_source_active]
  exact energy_active (restoredError s C R B τ t Q k Bp υ v) υ
    (fixedBadMask*ConcretePrimeRowBridge.idealGenerator ((R*C)*(Q^k))) 1 W₁ W₂ 0 v X₁ X₂ keep Φ K

section Ray
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {s : Input α} {η₀ : Character} {θ : α→RayQuotient.Characters M H}
  {w σ freq : α→ℝ} {W : ℝ→ℂ} {bslot Z : ℝ}

theorem matches_child (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Matches M H hH (child s C R B τ t) η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val)
      (fun i=>freq i.val) W bslot Z := by
  constructor
  · intro i I;exact h.character i.val I
  · intro i y;exact h.profile i.val y
  · intro i;exact h.pool i.val
  · intro i;exact h.scale i.val

theorem matches_twiceChild (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    Matches M H hH (twiceChild s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=>w i.val.val) (fun i=>σ i.val.val)
      (fun i=>freq i.val.val) W bslot Z :=
  matches_child M H hH (matches_child M H hH h C R B τ t) (Q^k) (R*C) Bp υ v

theorem active_common_ray_energy (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)))
    (J : Finset (liveIndices B.val)) (m A : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d : CenteredMomentEligibleEnergy.Data (liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    energy τ m A 0 W₁ W₂
      (fun i:remaining (activeInput s) C B L a J=>d.slots i.val)
      (fun i:remaining (activeInput s) C B L a J=>heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining (activeInput s) C B L a J=>d.P i.val) X₁ X₂ keep Φ K=
    energy τ m A 0 W₁ W₂
      (fun i:originalImage s C (restoreAllocation s C B) L a J=>primePool M H bslot (Z^(w i)))
      (fun i:originalImage s C (restoreAllocation s C B) L a J=>fun I=>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i:originalImage s C (restoreAllocation s C B) L a J=>Z^(w i)) X₁ X₂ keep Φ K :=
  (common_energy_active s C R B τ v L a J m A W₁ W₂ X₁ X₂ keep Φ K).trans
    (common_energy h τ v C R (restoreAllocation s C B) L a J m A W₁ W₂ X₁ X₂ keep Φ K)

theorem restoredError_matches (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    Matches M H hH (restoredError s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=>w i.val.val) (fun i=>σ i.val.val)
      (fun i=>freq i.val.val) W bslot Z :=
  matches_twiceChild M H hH h C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v

end Ray
end SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

end

end OAI

end Source1883

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAmplifiedCapacityCommon.lean; sha256: 84efcfb743ae1d807ab42f4939495b122a373ebe025861e4d83dcf84bfa163a8 -/
section Source1884
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplifiedCapacitySource CenteredMomentSourceLiveColumn
open CenteredMomentSecondCapacitySourceShift CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondNonexceptionalScalar
open CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondPhysicalCost CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentAllocatedChildCapacity CenteredMomentFirstScale
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def envelopeRef (qref:ℝ)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  (fixedFactor:ℝ)*qref*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)

def ratioPenalty (n:Fin 4→ℤ):ℝ:=
  max 1 (1/(dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))

lemma envelope_pos (qref:ℝ)(hq:0<qref)(C D:Ideal O)(hC:Supported C)
    (U:Finset (CommonIndex C D))(n:Fin 4→ℤ):0<envelopeRef qref C D U n:=by
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hu:=CenteredMomentSecondPhysicalLedger.common_product_pos C D hC U
  have hv:=norm_pos (Ideal.span {nonunitFrequencyGenerator C D U})
    (Ideal.span_singleton_eq_bot.not.mpr (nonunitFrequencyGenerator_ne_zero C D hC U))
  have hn:=dyadicScale_pos (n 1)
  unfold envelopeRef
  positivity

lemma adjusted_log (Z qref:ℝ)(hq:0<qref)(C D:Ideal O)(hC:Supported C)
    (U:Finset (CommonIndex C D))(n:Fin 4→ℤ):
    Real.logb Z (adjustedEnvelopeRef qref C D U n)=
      Real.logb Z (envelopeRef qref C D U n)+Real.logb Z (ratioPenalty n):=by
  exact Real.logb_mul (envelope_pos qref hq C D hC U n).ne'
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).ne'

theorem common_raw_reference_shift (s:Input ι)(υ:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (B:actualAllocations s.pools C)(hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K a Z qref:ℝ)(n:Fin 4→ℤ)(hq:0<qref)(hK:0<K)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*volume s≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s υ t) C R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
        (Fintype.card ι:ℝ)*Real.logb Z (max 1 s.upper)+Real.logb Z (ratioPenalty n) := by
  have hg:=actual_capacity_shift_reference υ t S β C D hC hD hCD U R rows W K
    (volume s) a Z qref n hq hK (volume_pos s) ha hZ hlower hne
  have hu:=common_volume_le (Fintype.card ι) (max 1 s.upper) (le_max_left _ _) s
    le_rfl (le_max_right _ _) C R0 B υ t hB
  have hc:=norm_pos C hC.1
  have hl:=Real.logb_le_logb_of_le hZ (volume_pos (child s C R0 B υ t)) hu
  have hb:0<max 1 s.upper:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [Real.logb_div (mul_pos (pow_pos hb _) (volume_pos s)).ne' hc.ne',
    Real.logb_mul (pow_pos hb _).ne' (volume_pos s).ne',Real.logb_pow] at hl
  rw [adjusted_log Z qref hq C D hC U n,Real.logb_div (volume_pos s).ne' hc.ne'] at hg
  have he:preVolume (commonData (withHeight s υ t) C R0 B)=volume (child s C R0 B υ t):=rfl
  rw [he]
  linarith

theorem common_raw_reference_shift_right (s:Input ι)(υ:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (B:actualAllocations s.pools D)(hB:frozenCoefficient B.val D R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K a Z qref:ℝ)(n:Fin 4→ℤ)(hq:0<qref)(hK:0<K)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*volume s≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s υ t) D R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
        (Fintype.card ι:ℝ)*Real.logb Z (max 1 s.upper)+Real.logb Z (ratioPenalty n) := by
  have hg:=actual_capacity_shift_reference_right υ t S β C D hC hD hCD U R rows W K
    (volume s) a Z qref n hq hK (volume_pos s) ha hZ hlower hne
  have hu:=common_volume_le (Fintype.card ι) (max 1 s.upper) (le_max_left _ _) s
    le_rfl (le_max_right _ _) D R0 B υ t hB
  have hc:=norm_pos D hD.1
  have hl:=Real.logb_le_logb_of_le hZ (volume_pos (child s D R0 B υ t)) hu
  have hb:0<max 1 s.upper:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [Real.logb_div (mul_pos (pow_pos hb _) (volume_pos s)).ne' hc.ne',
    Real.logb_mul (pow_pos hb _).ne' (volume_pos s).ne',Real.logb_pow] at hl
  rw [adjusted_log Z qref hq C D hC U n,Real.logb_div (volume_pos s).ne' hc.ne'] at hg
  have he:preVolume (commonData (withHeight s υ t) D R0 B)=volume (child s D R0 B υ t):=rfl
  rw [he]
  linarith

theorem actual_width_le_reference {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayFourExpansion.RayCharacter→Character}
    (hf:Family η C D hC hD U τ)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (qref Z:ℝ)(hq:(η.modulus.absNorm:ℝ)≤qref)(hZ:1<Z)(χ:RayFourExpansion.RayCharacter):
    Real.logb Z ((τ χ).modulus.absNorm:ℝ)+Real.logb Z (dyadicScale (n 1))≤
      Real.logb Z (envelopeRef qref C D U n) := by
  have hqpos:=norm_pos (τ χ).modulus (τ χ).modulus_ne_bot
  have he:=family_child_envelope hf t S β R rows W K hK n hne χ
  have hb:childEnvelope η C D U n≤envelopeRef qref C D U n:=by
    unfold childEnvelope envelopeRef
    gcongr
    exact (dyadicScale_pos _).le
  have hh:=Real.logb_le_logb_of_le hZ (mul_pos hqpos (dyadicScale_pos _)) (he.trans hb)
  rwa [Real.logb_mul hqpos.ne' (dyadicScale_pos _).ne'] at hh

end SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

end

end OAI

end Source1884

/- Original source: OAI/NumberTheory/DirichletL/Energy/AmplifiedChildWidth.lean; sha256: 70d2a04389f6f3fdeb654f1b558adfd1006794cf9d2bda2d1edf7038222961a1 -/
section Source1885
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyAmplifiedChildWidth
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAmplifiedActiveCapacitySource CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstAnnularInput CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondDyadicRowSupport CenteredMomentSecondRadicalBudget
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstScale CenteredMomentAmplifiedChildWidth
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι]
local instance {α:Type*}:DecidableEq α:=Classical.decEq _

lemma ball_support : Function.support (ballProfile:ℝ→ℂ)⊆Set.Iic (2:ℝ) := by
  intro x hx
  by_cases h:0≤x
  · exact (ballProfile_support_upper x h hx).le
  · exact (lt_of_not_ge h).le.trans (by norm_num)

theorem actual_ball_witness (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z:O,z≠0 ∧ ballProfile (normValue z/dyadicScale (n 1))=1 := by
  obtain ⟨z,_,hz,hz0,_⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U R rows W K n hne
  refine ⟨z,hz0,ballProfile_one _ (div_nonneg (normValue_pos z hz0).le (dyadicScale_pos _).le) ?_⟩
  exact (div_le_one (dyadicScale_pos _)).mpr (dyadicRows_norm rows n z hz).2.le

def geometry (N:ℕ)(b:ℝ):ℝ := (b^N)^2

lemma geometry_pos (N:ℕ)(b:ℝ)(hb:1≤b):0<geometry N b := by
  unfold geometry
  exact sq_pos_of_pos (pow_pos (zero_lt_one.trans_le hb) _)

lemma main_nominal_cap (N:ℕ)(b:ℝ)(hb:1≤b)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t K:ℝ)(hK:0<K)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    nominal (child s C R B τ t) K≤geometry N b*((volume s/(C.absNorm:ℝ))^2/K) := by
  have hv:=common_volume_le N b hb s hc hs C R B τ t hne
  have hC:=CenteredMomentAmplificationChildSourceCaps.norm_ge_one C (allocation_ne s C B)
  have hh:0≤volume s/(C.absNorm:ℝ):=div_nonneg (volume_pos s).le (by positivity)
  have hv':volume (child s C R B τ t)≤b^N*(volume s/(C.absNorm:ℝ)):=by simpa only [mul_div_assoc] using hv
  have hp:volume (child s C R B τ t)^2≤(b^N)^2*(volume s/(C.absNorm:ℝ))^2:=by
    nlinarith [volume_pos (child s C R B τ t),mul_nonneg (pow_nonneg (zero_le_one.trans hb) N) hh]
  exact (div_le_div_of_nonneg_right hp hK.le).trans_eq (by unfold geometry;ring)

lemma error_volume_cap (N:ℕ)(b:ℝ)(hb:1≤b)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (hslot:∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))(υ:Character)(v:ℝ) :
    volume (errorInput s C R B τ t Q k Bp υ v)≤
      b^N*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
  have hv:=common_volume_le N b hb s hc hs C R B τ t hne
  have hq:0≤(Q.absNorm:ℝ)^k:=pow_nonneg (Nat.cast_nonneg _) _
  have hh:=div_le_div_of_nonneg_right hv hq
  rw [common_volume] at hh
  rw [active_error_volume s C R B τ t Q hQ k hslot Bp υ v]
  convert hh using 1 <;> ring

lemma error_nominal_cap (N:ℕ)(b:ℝ)(hb:1≤b)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (hslot:∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ:Character)(v K:ℝ)(hK:0<K) :
    nominal (errorInput s C R B τ t Q k Bp υ v) K≤
      geometry N b*((volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k))^2/K) := by
  have hv:=error_volume_cap N b hb s hc hs C R B τ t hne Q hQ k hslot Bp υ v
  have hh:0≤volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k):=
    div_nonneg (volume_pos s).le (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
  have hp:volume (errorInput s C R B τ t Q k Bp υ v)^2≤
      (b^N)^2*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k))^2:=by
    nlinarith [volume_pos (errorInput s C R B τ t Q k Bp υ v),
      mul_nonneg (pow_nonneg (zero_le_one.trans hb) N) hh]
  exact (div_le_div_of_nonneg_right hp hK.le).trans_eq (by unfold geometry;ring)

lemma restored_nominal_eq (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (hslot:∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ:Character)(v K:ℝ) :
    nominal (restoredError s C R B τ t Q k Bp υ v) K=
      nominal (errorInput s C R B τ t Q k Bp υ v) K := by
  unfold nominal
  rw [restoredError_volume s C R B τ t Q hQ k hslot Bp υ v,
    active_error_volume s C R B τ t Q hQ k hslot Bp υ v]

def mainRadius (C D:Ideal O)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ):ℝ :=
  mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V))
    (Real.logb Z (C.absNorm:ℝ)) σ δ reserve

def errorRadius (C D:Ideal O)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ)(p:O)(k:ℕ):ℝ :=
  errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V))
    (Real.logb Z (C.absNorm:ℝ)) σ δ reserve p k

lemma mainRadius_eq (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ):
    mainRadius C D E K V Z σ δ reserve=
      mainCommonRadius Z (Real.logb Z ((commonPart D C).absNorm:ℝ))
        (nominalLog C D (∏P∈E,P.val) K V Z)
        (Real.logb Z ((commonPart C D).absNorm:ℝ)) σ δ reserve := by
  rw [commonPart_eq_left C D hC.1 hCD,commonPart_eq_left D C hD.1 hCD.symm]
  simp only [mainRadius,nominalLog,primeSubsetGenerator,span_idealGenerator]

lemma errorRadius_eq (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ)(p:O)(k:ℕ):
    errorRadius C D E K V Z σ δ reserve p k=
      errorCommonRadius Z (Real.logb Z ((commonPart D C).absNorm:ℝ))
        (nominalLog C D (∏P∈E,P.val) K V Z)
        (Real.logb Z ((commonPart C D).absNorm:ℝ)) σ δ reserve p k := by
  rw [commonPart_eq_left C D hC.1 hCD,commonPart_eq_left D C hD.1 hCD.symm]
  simp only [errorRadius,nominalLog,primeSubsetGenerator,span_idealGenerator]

def threshold (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ):ℝ :=
  fixedWidthThreshold 2 (geometry N b) σ (by norm_num) (geometry_pos N b hb) hσ

lemma threshold_gt_one (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ):1<threshold N b σ hb hσ :=
  (fixedWidthThreshold_spec 2 (geometry N b) σ (by norm_num) (geometry_pos N b hb) hσ).1

theorem main_child_width (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ)
    (Z:ℝ)(hlarge:threshold N b σ hb hσ≤Z)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C D R:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(τ:Character)(t:ℝ)
    (hB:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (K δ reserve ξ q Mparent:ℝ)(hK:0<K)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hη:(s.η.modulus.absNorm:ℝ)≤Z^q)(hparent:Real.logb Z K+q≤Mparent)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)(hC₂:Supported C₂)(hD₂:Supported D₂)
    (U:Finset (CommonIndex C₂ D₂))(family:RayCharacter→Character)
    (hf:Family τ C₂ D₂ hC₂ hD₂ U family)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hne:physicalBlock τ t S β C₂ D₂ hC₂ hD₂ U
      (frequencyRadius (nominal (child s C R B τ t) (mainRadius C D E K (volume s) Z σ δ reserve)) Z ξ)
      rows W (mainRadius C D E K (volume s) Z σ δ reserve) n≠0)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)<Mparent-σ/2 := by
  have hZ:1<Z:=(threshold_gt_one N b σ hb hσ).trans_le hlarge
  let L:=mainRadius C D E K (volume s) Z σ δ reserve
  have hL:0<L:=by unfold L mainRadius mainCommonRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have he:=mainRadius_eq C D hC hD hCD E K (volume s) Z σ δ reserve
  have hscale:=main_nominal_cap N b hb s hc hs C R B τ t L hL hB
  have hhscale:nominal (child s C R B τ t) L≤geometry N b*
      ((volume s/((commonPart C D).absNorm:ℝ))^2/L):=by
    simpa only [commonPart_eq_left C D hC.1 hCD] using hscale
  obtain ⟨z,hz,hball⟩:=actual_ball_witness τ t S β C₂ D₂ hC₂ hD₂ U _ rows W L n hne
  have hw:=main_declared_width_drop s.η τ fixedBadMask fixedBadMask_ne_zero C D E
    K (volume s) Z σ δ reserve hK (volume_pos s) hZ hmod hf t S β rows W
    (nominal (child s C R B τ t) L) (geometry N b) ξ (nominal_pos _ L hL)
    (geometry_pos N b hb) (by simpa only [←he] using hhscale) n
    (by simpa only [←he] using hne) χ ballProfile 2 (by norm_num) ball_support z hz
    (by rw [hball];exact one_ne_zero) rfl q hη hσ hδ hr hξ hlarge
  have hlog:Real.logb Z (dyadicScale (n 1))≤Real.logb Z (max 1 (2*dyadicScale (n 1))):=by
    apply Real.logb_le_logb_of_le hZ (dyadicScale_pos _)
    exact (by linarith [dyadicScale_pos (n 1)]:dyadicScale (n 1)≤2*dyadicScale (n 1)).trans (le_max_right _ _)
  linarith

theorem error_child_width (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ)
    (Z:ℝ)(hlarge:threshold N b σ hb hσ≤Z)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C D R:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(τ:Character)(t:ℝ)
    (hB:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=0∨k=5∨k=6)
    (hslot:∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^(k+1)))
    (υ:Character)(χ₀:RayCharacter)(v:ℝ)
    (hN:υ.modulus.absNorm≤radicalBound (childCharacter τ χ₀) fixedBadMask p (errorMovingExponent k))
    (K δ reserve ξ q Mparent:ℝ)(hK:0<K)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hη:(s.η.modulus.absNorm:ℝ)≤Z^q)(hparent:Real.logb Z K+q≤Mparent)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)(hC₂:Supported C₂)(hD₂:Supported D₂)
    (U:Finset (CommonIndex C₂ D₂))(family:RayCharacter→Character)
    (hf:Family υ C₂ D₂ hC₂ hD₂ U family)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U
      (frequencyRadius (nominal (errorInput s C R B τ t (Ideal.span {p}) (k+1) Bp υ v)
        (errorRadius C D E K (volume s) Z σ δ reserve p (k+1))) Z ξ)
      rows W (errorRadius C D E K (volume s) Z σ δ reserve p (k+1)) n≠0)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)<Mparent-σ/2 := by
  have hZ:1<Z:=(threshold_gt_one N b σ hb hσ).trans_le hlarge
  have hQ:Ideal.span {p}≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  let L:=errorRadius C D E K (volume s) Z σ δ reserve p (k+1)
  have hL:0<L:=by unfold L errorRadius errorCommonRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have he:=errorRadius_eq C D hC hD hCD E K (volume s) Z σ δ reserve p (k+1)
  have hscale:=error_nominal_cap N b hb s hc hs C R B τ t hB (Ideal.span {p}) hQ (k+1) hslot Bp υ v L hL
  have hpn:((Ideal.span {p}).absNorm:ℝ)=normValue p:=rfl
  have hhscale:nominal (errorInput s C R B τ t (Ideal.span {p}) (k+1) Bp υ v) L≤geometry N b*
      ((volume s/((commonPart C D).absNorm*(normValue p)^(k+1)))^2/L):=by
    simpa only [commonPart_eq_left C D hC.1 hCD,hpn] using hscale
  obtain ⟨z,hz,hball⟩:=actual_ball_witness υ v S β C₂ D₂ hC₂ hD₂ U _ rows W L n hne
  have hw:=error_declared_width_drop s.η τ fixedBadMask fixedBadMask_ne_zero C D E
    K (volume s) Z σ δ reserve hK (volume_pos s) hZ hmod υ χ₀ p hp k hk hN hf v S β rows W
    (nominal (errorInput s C R B τ t (Ideal.span {p}) (k+1) Bp υ v) L) (geometry N b) ξ
    (nominal_pos _ L hL) (geometry_pos N b hb) (by simpa only [←he] using hhscale) n
    (by simpa only [←he] using hne) χ ballProfile 2 (by norm_num) ball_support z hz
    (by rw [hball];exact one_ne_zero) rfl q hη hσ hδ hr hξ hlarge
  have hlog:Real.logb Z (dyadicScale (n 1))≤Real.logb Z (max 1 (2*dyadicScale (n 1))):=by
    apply Real.logb_le_logb_of_le hZ (dyadicScale_pos _)
    exact (by linarith [dyadicScale_pos (n 1)]:dyadicScale (n 1)≤2*dyadicScale (n 1)).trans (le_max_right _ _)
  linarith

end SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

end

end OAI

end Source1885

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalSourceFixedSource.lean; sha256: 440445529fa18742648459c1e9ae97d34db4fa0cf4567a8d3cb8513db6e7e469 -/
section Source1886
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalPrefactor CenteredMomentCommonSupport CenteredMomentConjugateWindow
open CenteredMomentChildAssembly RayFourExpansion CompletedGauss CenteredMomentGaussEnergy FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstFixedSourceDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

variable {η:Character}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem FixedPair.left_column (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)(t:ℝ)(L:Ideal O)
    (I:columns C C hC.1 s.columns):
    divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t s.beta C a*
        leftCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C C hC.1 s.columns a)) ξ₁ I=
      (if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff F.left t I:=
  fixed_divisor_column s η F.left C _ ξ₁ F.left_height L I
    (column_supported C C hC.1 s.columns I) t

theorem FixedPair.right_column (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (s:OriginalData ι)(t:ℝ)(L:Ideal O)(I:columns C D hD.1 s.columns):
    divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t s.beta D a*
        rightCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C D hD.1 s.columns a)) ξ₂ I=
      (if L∣(I:Ideal O) then s.beta (D*I) else 0)*heightCoeff F.right t I:=
  fixed_divisor_column s η F.right D _ ξ₂ F.right_height L I
    (column_supported C D hD.1 s.columns I) t

theorem FixedPair.original_data (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)(hsC:s.s∣C)(hsD:s.s∣D)
    (t T:ℝ)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*leftChild s η (fixedBadMask*idealGenerator s.R) t C D hC E ξ₁ L z=
      allocatedPolynomial s C L F.left t T z ∧
    (Real.sqrt T:ℂ)⁻¹*rightChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L (-z)=
      allocatedPolynomial s D L F.right t T (-z):=by
  constructor
  · exact first_column_original_data s hS hp C hC hsC F.left t T L _ (F.left_column s t L) z
  · exact first_column_original_data_filter s hS hp C D hC.1 hD hCD hsD F.right t T L _
      (F.right_column hD s t L) (-z)

theorem FixedPair.window_integrals (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)(hsC:s.s∣C)(hsD:s.s∣D)
    (t T θ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁:ℝ→ℂ)(hV₁c:HasCompactSupport V₁)(hV₁s:ContDiff ℝ ∞ V₁)
    (V₂:ℝ→ℂ)(hV₂c:HasCompactSupport V₂)(hV₂s:ContDiff ℝ ∞ V₂)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*leftWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC E ξ₁ L θ X V₁ z=
      (∫w:ℝ,columnDensity V₁ hV₁c hV₁s w*logPhase (θ-w) (Real.log X)*
        allocatedPolynomial s C L F.left (t+2*Real.pi*(w-θ)) T z) ∧
    (Real.sqrt T:ℂ)⁻¹*rightWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L θ Y V₂ (-z)=
      (∫w:ℝ,columnDensity (fun x=>star (V₂ x)) (conjugate_compact V₂ hV₂c)
        (conjugate_smooth V₂ hV₂s) w*logPhase (-θ-w) (Real.log Y)*
        allocatedPolynomial s D L F.right (t+2*Real.pi*(w-(-θ))) T (-z)):=by
  constructor
  · exact column_window_original_integral s hS hp C C hC.1 hC rfl hsC F.left t T θ X hX
      V₁ hV₁c hV₁s L _ (F.left_column s t L) z
  · exact column_star_window_original_integral s hS hp C D hC.1 hD hCD hsD F.right t T θ Y hY
      V₂ hV₂c hV₂s L _ (F.right_column hD s t L) z

theorem FixedPair.scalar_conductors (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (K A₀ B₀ a T M:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(ha:0<a)(hT:0<T)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)(hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖*T/((C.absNorm:ℝ)*D.absNorm)*
      Real.sqrt ((F.left.modulus.absNorm:ℝ)*F.right.modulus.absNorm)≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)/
        (CenteredMomentRankinRadical.commonRadical C D).absNorm:=by
  exact actual_scalar_conductors C D hC hD E η F.left F.right K A₀ B₀ a T M fixedPresentationCost
    hK hA hB ha hT fixedPresentationCost_pos.le hl hr F.conductor_caps.1 F.conductor_caps.2

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI

end Source1886

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalDyadicRows.lean; sha256: bb293402f045ee53be0c4eef0bf33b0867f5e81decb392928e664b728313b913 -/
section Source1887
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicRows
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentRowNorm
local notation "O" => HeckeFamily.O

def activeRows (rows : Finset O) (n : Fin 4→ℤ) : Finset O :=
  rows.filter (fun h => h∈dyadRows (n 1))

lemma mem_activeRows (rows : Finset O) (n : Fin 4→ℤ) (h : O) :
    h∈activeRows rows n ↔ h∈rows ∧ dyadicWeight (n 1) (normValue h)≠0 := by
  simp only [activeRows,Finset.mem_filter,mem_dyadRows]

lemma activeRows_subset (rows : Finset O) (n : Fin 4→ℤ) : activeRows rows n⊆rows :=
  Finset.filter_subset _ _

lemma activeRows_nonzero (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) : h≠0 :=
  dyadRows_ne_zero (n 1) h (Finset.mem_filter.mp hh).2

lemma activeRows_norm (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) :
    1≤normValue h ∧ dyadicScale (n 1)/4<normValue h ∧ normValue h<dyadicScale (n 1) :=
  ⟨normValue_ge_one h (activeRows_nonzero rows n h hh),
    dyadicWeight_support (n 1) ((mem_activeRows rows n h).mp hh).2⟩

lemma activeRows_scale_gt_one (rows : Finset O) (n : Fin 4→ℤ)
    (hne : (activeRows rows n).Nonempty) : 1<dyadicScale (n 1) := by
  obtain ⟨h,hh⟩:=hne
  exact (activeRows_norm rows n h hh).1.trans_lt (activeRows_norm rows n h hh).2.2

lemma activeRows_ball_majorant (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) :
    1≤(ballProfile (‖eisEmbedding h‖^2/dyadicScale (n 1))).re :=
  ballProfile_majorizes _ (dyadicScale_pos (n 1)) h (activeRows_norm rows n h hh).2.2.le

lemma row_log_window (n : ℤ) (h : O) :
    logAnnulus (Real.log (‖eisEmbedding h‖^2/dyadicScale n)) =
      (dyadicWeight n (normValue h):ℂ) := by
  by_cases hh : h=0
  · subst h
    simp only [map_zero,norm_zero,zero_pow (by decide : 2≠0),zero_div,Real.log_zero,
      logAnnulus,Real.exp_zero]
    rw [annulus_zero_high 1 le_rfl]
    rw [show normValue (0:O)=0 by simp [normValue_eq_embedding],
      dyadicWeight_zero_nonpos n 0 le_rfl,Complex.ofReal_zero]
  · rw [←normValue_eq_embedding]
    exact (actual_dyadic_log_window n (normValue h)
      (zero_lt_one.trans_le (normValue_ge_one h hh))).symm

theorem block_activeRows (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    block η m A t S c C D hC hD E rows W (fun _=>logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) =
    block η m A t S c C D hC hD E (activeRows rows n) W (fun _=>logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  unfold block activeRows
  dsimp only
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hd : h∈dyadRows (n 1)
  · simp only [hd,ite_true]
  · have hw : dyadicWeight (n 1) (normValue h)=0 := by
      simpa only [mem_dyadRows,not_not] using hd
    simp only [hd,windows,row_log_window,hw,Complex.ofReal_zero,
      mul_zero,zero_mul,ite_self,Finset.sum_const_zero]

end SevenEighths.CenteredMomentFirstPhysicalDyadicRows

end

end OAI

end Source1887

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAmplifiedRadiusLower.lean; sha256: 4a088d33d2386ad17e18ecd8252b76cd1d0ae116b09616915bc0f82ef8da6175 -/
section Source1888
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedRadiusLower
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstScale
open CenteredMomentFirstPhysicalDyadicRows
local notation "O" => ActualEisensteinCubic.O

lemma base_radius_identity (Z K0 Csec xi : ℝ) (hZ : 1<Z) (hC : 0<Csec) :
    Z^(K0+frequencyLoss Z (32*Csec) xi)=128*Csec*Z^K0*Z^(xi/2) := by
  have h := source_enclosure_power Z (32*Csec) K0 xi 1 hZ (by positivity) zero_lt_one
  simpa only [Real.logb_one,sub_zero,div_one] using h.symm.trans (by ring)

lemma retained_base_le (Z K0 Csec Tsec xi H0 : ℝ) (hZ : 1<Z) (hC : 0<Csec)
    (hsec : Tsec≤Csec*Z^K0) (hrow : H0≤4*frequencyRadius Tsec Z xi) :
    H0≤Z^(K0+frequencyLoss Z (32*Csec) xi) := by
  rw [base_radius_identity Z K0 Csec xi hZ hC]
  have hp : 0≤Z^(xi/2) := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  have hq : 0≤Z^K0 := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  calc
    H0≤4*(Tsec*Z^(xi/2)) := hrow
    _≤4*((Csec*Z^K0)*Z^(xi/2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsec hp) (by norm_num)
    _≤128*Csec*Z^K0*Z^(xi/2) := by nlinarith [mul_nonneg (mul_nonneg hC.le hq) hp]

theorem common_radii_lower (Z d K0 c sigma reserve Csec Tsec xi H0 : ℝ)
    (hZ : 1<Z) (hC : 0<Csec) (hsigma : 0≤sigma) (hreserve : 0≤reserve)
    (hsec : Tsec≤Csec*Z^K0) (hrow : H0≤4*frequencyRadius Tsec Z xi)
    (p : O) (k : ℕ) :
    H0≤mainCommonRadius Z d K0 c sigma (frequencyLoss Z (32*Csec) xi) reserve ∧
    H0≤errorCommonRadius Z d K0 c sigma (frequencyLoss Z (32*Csec) xi) reserve p k := by
  have hb := retained_base_le Z K0 Csec Tsec xi H0 hZ hC hsec hrow
  constructor
  · apply hb.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [le_max_right (d-c) (0:ℝ)]
  · apply hb.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [le_max_right (d-c-2*errorRemoval p Z k+errorMoving p Z k) (0:ℝ)]

theorem actual_retained_radii_lower (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi d c sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 0<Csec)
    (hsigma : 0≤sigma) (hreserve : 0≤reserve)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) (p : O) (k : ℕ) :
    dyadicScale n≤mainCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve ∧
    dyadicScale n≤errorCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve p k := by
  apply common_radii_lower Z d _ c sigma reserve Csec Tsec xi _ hZ hC hsigma hreserve
  · simpa only [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (firstNominalScale_pos I J E hE K X hK hX)] using hsec
  · exact retained_scale_le _ n hn

theorem active_row_reciprocals (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi d c sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 0<Csec)
    (hsigma : 0≤sigma) (hreserve : 0≤reserve)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (rows : Finset O) (n : Fin 4→ℤ)
    (hn : Retained (frequencyRadius Tsec Z xi) (n 1))
    (hne : (activeRows rows n).Nonempty) (p : O) (k : ℕ) :
    (mainCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve)⁻¹≤1 ∧
    (errorCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve p k)⁻¹≤1 := by
  have hb := actual_retained_radii_lower I J E hE K X Z Csec Tsec xi d c sigma reserve
    hK hX hZ hC hsigma hreserve hsec (n 1) hn p k
  have ho := (activeRows_scale_gt_one rows n hne).le
  exact ⟨inv_le_one_of_one_le₀ (ho.trans hb.1),inv_le_one_of_one_le₀ (ho.trans hb.2)⟩

end SevenEighths.CenteredMomentFirstAmplifiedRadiusLower

end

end OAI

end Source1888

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSecondCommonGates.lean; sha256: d652f792fecb32a7f1908295880b3d9b1eae4397f3f596643f332618dae9a5eb -/
section Source1889
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSecondInputGates
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
local instance {α:Type*}:DecidableEq α:=Classical.decEq _

def commonExponent (A D P C q ε ξ:ℝ):ℝ:=
  max (A+ε) (max (2*A+D+ε+ξ/2) (max (P+C) q))

theorem eventually_common_ready (N:ℕ)(b b₁ b₂ ε:ℝ)
    (hb:1≤b)(hb₁:1≤b₁)(hb₂:1≤b₂)(hε:0<ε):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t:ℝ),
    R≠0 → frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀K A D P Ccap q ξ:ℝ,0<K → 0≤ξ → volume s≤Z^A → K⁻¹≤Z^D →
    (R.absNorm:ℝ)≤Z^P → (C.absNorm:ℝ)≤Z^Ccap → (τ.modulus.absNorm:ℝ)≤Z^q →
    Ready (child s C R B τ t) (R*C) K Z ξ (commonExponent A D P Ccap q ε ξ):=by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε
    (geometry_ge_one N b b₁ b₂ hb hb₁ hb₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hs he C R B τ t hR hB K A D P Ccap q ξ hK hξ hV hKi hRN hCN hτ
  have hC:=allocation_ne s C B
  have hNc:=norm_ge_one C hC
  have hv:=volume_pos s
  have hbN:0≤b^N:=pow_nonneg (zero_le_one.trans hb) _
  have hcv:volume (child s C R B τ t)≤b^N*volume s:=
    (common_volume_le N b hb s hs he.1 C R B τ t hB).trans
      (div_le_self (mul_nonneg hbN hv.le) hNc)
  have hr:=radius_bound N b b₁ b₂ hb hb₁ hb₂ (child s C R B τ t)
    ((live_card_le B.val).trans hs) (endpoints_child b b₁ b₂ s he C R B τ t)
  have hVg:volume (child s C R B τ t)≤geometry N b b₁ b₂*volume s:=by
    apply hcv.trans
    apply mul_le_mul_of_nonneg_right _ hv.le
    apply (pow_le_pow_right₀ hb (show N≤2*N by omega)).trans
    unfold geometry
    exact (le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hb) _) hb₁).trans
      (le_mul_of_one_le_right (by positivity) hb₂)
  have hHg:sourceRadius (child s C R B τ t)≤geometry N b b₁ b₂*volume s:=by
    apply hr.2.trans
    apply (mul_le_mul_of_nonneg_left hcv (show 0≤b^N*b₁*b₂ by positivity)).trans_eq
    unfold geometry
    rw [show 2*N=N+N by omega,pow_add]
    ring
  have hc:=polynomial_caps (geometry N b b₁ b₂) (volume s)
    (volume (child s C R B τ t)) (sourceRadius (child s C R B τ t)) K Z A D ε ξ
    (geometry_ge_one N b b₁ b₂ hb hb₁ hb₂) hZ.1 hZ.2.2 hv (volume_pos _) hr.1 hK
    hVg hHg hV hKi
  have h₁:A+ε≤commonExponent A D P Ccap q ε ξ:=le_max_left _ _
  have h₂:2*A+D+ε+ξ/2≤commonExponent A D P Ccap q ε ξ:=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₃:P+Ccap≤commonExponent A D P Ccap q ε ξ:=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h₄:q≤commonExponent A D P Ccap q ε ξ:=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hpow {x y:ℝ}(h:x≤y):Z^x≤Z^y:=Real.rpow_le_rpow_of_exponent_le hZ.1.le h
  have hRC:((R*C).absNorm:ℝ)≤Z^(P+Ccap):=by
    rw [map_mul,Nat.cast_mul,Real.rpow_add (zero_lt_one.trans hZ.1)]
    exact mul_le_mul hRN hCN (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hZ.1.le) P)
  refine ⟨mul_ne_zero hR hC,hK,hc.1.trans (hpow h₁),hr.1,hc.2.1.trans (hpow h₁),
    hτ.trans (hpow h₄),hRC.trans (hpow h₃),nominal_pos _ K hK,
    hc.2.2.1.trans (hpow ((by linarith : 2*A+D+ε≤2*A+D+ε+ξ/2).trans h₂)),
    hc.2.2.2.1,hc.2.2.2.2.trans (hpow h₂)⟩

end SevenEighths.CenteredMomentFirstSecondInputGates

end

end OAI

end Source1889

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondInputCapacitySource.lean; sha256: b58b289cceacf7b32521bad372ab6b5321933e4ec48de7815540347f17cd0ffc -/
section Source1890
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondInputCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAllocatedChildCapacity
open CenteredMomentFirstAmplifiedCapacityCommon CenteredMomentSourceLiveColumn
open CenteredMomentSecondCapacitySourceShift CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonHeightEnvelope
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def lowerFactor (N:ℕ)(slotLower plainLower:ℝ):ℝ:=
  (min 1 slotLower)^N*plainLower^2

lemma lowerFactor_pos (N:ℕ)(slotLower plainLower:ℝ)(hs:0<slotLower)(hp:0<plainLower):
    0<lowerFactor N slotLower plainLower:=by unfold lowerFactor;positivity

theorem actual_lower_support (N:ℕ)(slotLower plainLower:ℝ)(hs:0<slotLower)(hp:0<plainLower)
    (s:Input ι)(hc:Fintype.card ι≤N)(hlo:slotLower≤s.lower)
    (hW₁:∀x,s.W₁ x≠0→plainLower≤x)(hW₂:∀x,s.W₂ x≠0→plainLower≤x)
    (R seed I:Ideal O)(hne:coefficient s R seed I≠0):
    lowerFactor N slotLower plainLower*volume s≤(I.absNorm:ℝ):=by
  have hm:0≤min 1 slotLower:=(lt_min zero_lt_one hs).le
  have hprod:(min 1 slotLower)^N≤∏i,s.lo i:=by
    apply (pow_le_pow_of_le_one hm (min_le_left _ _) hc).trans
    have hh:=Finset.prod_le_prod₀ (s:=Finset.univ) (f:=fun _:ι=>min 1 slotLower)
      (g:=fun i=>s.lo i) (fun _ _=>hm)
      (fun i _=>(min_le_right _ _).trans (hlo.trans (s.lower_le i)))
    simpa only [Finset.prod_const,Finset.card_univ] using hh
  have hh:=original_column_lower s R seed I plainLower plainLower hp.le hp.le hW₁ hW₂ hne
  change (∏i,s.lo i)*plainLower*plainLower*volume s≤(I.absNorm:ℝ) at hh
  apply le_trans _ hh
  have hv:0≤volume s:=(volume_pos s).le
  unfold lowerFactor
  nlinarith [mul_le_mul_of_nonneg_right hprod (mul_nonneg (sq_nonneg plainLower) hv)]

lemma upper_log_cost (N:ℕ)(b Z:ℝ)(hb:1≤b)(hZ:1<Z)
    (s:Input ι)(hc:Fintype.card ι≤N)(hhi:s.upper≤b):
    (Fintype.card ι:ℝ)*Real.logb Z (max 1 s.upper)≤(N:ℝ)*Real.logb Z b:=by
  have hs:0<max 1 s.upper:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hl:=Real.logb_le_logb_of_le hZ hs (max_le hb hhi)
  have hn:(Fintype.card ι:ℝ)≤N:=by exact_mod_cast hc
  exact (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hn (Real.logb_nonneg hZ hb))

def fixedLoss (N:ℕ)(slotLower plainLower b Z:ℝ):ℝ:=
  Real.logb Z (4/((fixedFactor:ℝ)*(lowerFactor N slotLower plainLower)^2))+
    (N:ℝ)*Real.logb Z b

theorem actual_common_input_shift (N:ℕ)(slotLower plainLower b:ℝ)
    (hs:0<slotLower)(hp:0<plainLower)(hb:1≤b)
    (s:Input ι)(hc:Fintype.card ι≤N)(hlo:slotLower≤s.lower)(hhi:s.upper≤b)
    (hW₁:∀x,s.W₁ x≠0→plainLower≤x)(hW₂:∀x,s.W₂ x≠0→plainLower≤x)
    (R0 seed:Ideal O)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(B:actualAllocations s.pools C)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K Z qref:ℝ)(n:Fin 4→ℤ)(hq:0<qref)(hK:0<K)(hZ:1<Z)
    (hne:physicalBlock s.η s.t S (coefficient s R0 seed) C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s s.η s.t) C R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        fixedLoss N slotLower plainLower b Z+Real.logb Z (ratioPenalty n):=by
  have hlow:=fun I hI=>actual_lower_support N slotLower plainLower hs hp s hc hlo hW₁ hW₂ R0 seed I hI
  have hh:=common_raw_reference_shift s s.η s.t S (coefficient s R0 seed) C D R0 hC hD hCD
    B hB U R rows W K (lowerFactor N slotLower plainLower) Z qref n hq hK
    (lowerFactor_pos N slotLower plainLower hs hp) hZ hlow hne
  have hu:=upper_log_cost N b Z hb hZ s hc hhi
  unfold fixedLoss
  linarith

theorem actual_common_input_shift_right (N:ℕ)(slotLower plainLower b:ℝ)
    (hs:0<slotLower)(hp:0<plainLower)(hb:1≤b)
    (s:Input ι)(hc:Fintype.card ι≤N)(hlo:slotLower≤s.lower)(hhi:s.upper≤b)
    (hW₁:∀x,s.W₁ x≠0→plainLower≤x)(hW₂:∀x,s.W₂ x≠0→plainLower≤x)
    (R0 seed:Ideal O)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(B:actualAllocations s.pools D)
    (hB:frozenCoefficient B.val D R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K Z qref:ℝ)(n:Fin 4→ℤ)(hq:0<qref)(hK:0<K)(hZ:1<Z)
    (hne:physicalBlock s.η s.t S (coefficient s R0 seed) C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s s.η s.t) D R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        fixedLoss N slotLower plainLower b Z+Real.logb Z (ratioPenalty n):=by
  have hlow:=fun I hI=>actual_lower_support N slotLower plainLower hs hp s hc hlo hW₁ hW₂ R0 seed I hI
  have hh:=common_raw_reference_shift_right s s.η s.t S (coefficient s R0 seed) C D R0 hC hD hCD
    B hB U R rows W K (lowerFactor N slotLower plainLower) Z qref n hq hK
    (lowerFactor_pos N slotLower plainLower hs hp) hZ hlow hne
  have hu:=upper_log_cost N b Z hb hZ s hc hhi
  unfold fixedLoss
  linarith

theorem fixed_loss_eventually (N:ℕ)(slotLower plainLower b ε:ℝ)
    (hs:0<slotLower)(hp:0<plainLower)(hb:1≤b)(hε:0<ε):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ fixedLoss N slotLower plainLower b Z≤ε:=by
  have ha:=lowerFactor_pos N slotLower plainLower hs hp
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hb0:0<b:=zero_lt_one.trans_le hb
  let A:ℝ:=4/((fixedFactor:ℝ)*(lowerFactor N slotLower plainLower)^2)*b^N
  have hA:0<A:=by dsimp [A];positivity
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) A,eventually_gt_atTop (1:ℝ)] with Z hg hZ
  refine ⟨hZ,?_⟩
  have hl:=Real.logb_le_logb_of_le hZ hA hg
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hl
  dsimp [A] at hl
  rw [Real.logb_mul (by positivity) (pow_pos hb0 N).ne',Real.logb_pow] at hl
  exact hl

end SevenEighths.CenteredMomentSecondInputCapacitySource

end

end OAI

end Source1890

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstLiveAdmission.lean; sha256: 8f96102c7c485970bfd70711ee989cd282212c522722f1c61240f24a7d73f746 -/
section Source1891
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstLiveAdmission
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open ActualEisensteinCubic CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstSecondInputGates CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplifiedRadiusLower CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAnnularInput CenteredMomentSectorLocalization
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceConductorCaps
open CenteredMomentEnergyInputParentCapacity CenteredMomentEnergyBands
open CenteredMomentEnergyAmplifiedChildWidth CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentActiveSource
open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CompletedGauss RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentRowNorm
local notation "O" => HeckeFamily.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem first_block_active_rows_nonempty
    (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (rows : Finset O) (W : 𝓢(ℝ,ℂ))
    (K : ℝ) (n : Fin 4 → ℤ)
    (hne : block η m A t S c C D hC hD E rows W (fun _ => logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0) :
    (activeRows rows n).Nonempty := by
  by_contra h
  have he : activeRows rows n = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  apply hne
  rw [block_activeRows, he]
  simp only [block, Finset.sum_empty, mul_zero]

theorem original_both_columns {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed C D : Ideal O) (hseed : Squarefree seed)
    (hz₁ : s.W₁ 0 = 0) (hz₂ : s.W₂ 0 = 0)
    (hC : Supported C) (hD : Supported D)
    (hlabel : (C,D) ∈ CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed))))
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair s.η C D hC E ξ₁ ξ₂) (t T : ℝ) (L : Ideal O) (z : O) :
    (Real.sqrt T : ℂ)⁻¹ * leftChild (original s R seed) s.η
      (fixedBadMask*idealGenerator R) t C D hC E ξ₁ L z =
      allocatedPolynomial (original s R seed) C L F.left t T z ∧
    (Real.sqrt T : ℂ)⁻¹ * rightChild (original s R seed) s.η
      (fixedBadMask*idealGenerator R) t C D hC hD E ξ₂ L (-z) =
      allocatedPolynomial (original s R seed) D L F.right t T (-z) := by
  have hg := actual_common_gates s R seed hseed hz₁ hz₂ C D hlabel
  exact F.original_data hD hg.2.2.1 (original s R seed) s.pools_ne
    (fun i I hI => s.prime i I hI) hg.2.2.2.1 hg.2.2.2.2.1 t T L z

def columnIdeal (C D : Ideal O) (right : Bool) : Ideal O := if right then D else C

def oppositeIdeal (C D : Ideal O) (right : Bool) : Ideal O := if right then C else D

def columnMainRadius (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) (right : Bool) : ℝ :=
  mainCommonRadius Z (Real.logb Z ((oppositeIdeal C D right).absNorm : ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K V))
    (Real.logb Z ((columnIdeal C D right).absNorm : ℝ)) σ δ reserve

def columnErrorRadius (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) (right : Bool) (p : O) (k : ℕ) : ℝ :=
  errorCommonRadius Z (Real.logb Z ((oppositeIdeal C D right).absNorm : ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K V))
    (Real.logb Z ((columnIdeal C D right).absNorm : ℝ)) σ δ reserve p k

lemma columnMainRadius_left (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) :
    columnMainRadius C D E K V Z σ δ reserve false = mainRadius C D E K V Z σ δ reserve := rfl

lemma columnErrorRadius_left (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) (p : O) (k : ℕ) :
    columnErrorRadius C D E K V Z σ δ reserve false p k =
      errorRadius C D E K V Z σ δ reserve p k := rfl

def readyBudget (A P : ℝ) : ℝ := 4*A + P + 10

lemma readyBudget_nonneg (A P : ℝ) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    0 ≤ readyBudget A P := by unfold readyBudget; linarith

lemma common_exponent_le (A P ξ : ℝ) (hA : 0 ≤ A) (hP : 0 ≤ P) (hξ : ξ ≤ 1) :
    commonExponent A 0 P (A+1) (3*A+3) 1 ξ ≤ readyBudget A P := by
  unfold commonExponent readyBudget
  exact max_le (by linarith) (max_le (by linarith) (max_le (by linarith) (by linarith)))

lemma error_exponent_le (A P σ ξ : ℝ) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hσ : σ ≤ 1) (hξ : ξ ≤ 1) :
    exponent A 0 P (3*A+3+σ/3) 1 ξ ≤ readyBudget A P := by
  unfold exponent readyBudget
  exact max_le (by linarith) (max_le (by linarith) (max_le (by linarith) (by linarith)))

lemma ready_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Input ι) (R : Ideal O)
    (K Z ξ B B' : ℝ) (hZ : 1 ≤ Z) (hB : B ≤ B')
    (h : Ready s R K Z ξ B) : Ready s R K Z ξ B' := by
  have hp := Real.rpow_le_rpow_of_exponent_le hZ hB
  exact ⟨h.puncture_ne,h.scale_pos,h.volume_cap.trans hp,h.source_nonneg,
    h.source_cap.trans hp,h.conductor_cap.trans hp,h.puncture_cap.trans hp,
    h.nominal_pos,h.nominal_cap.trans hp,h.frequency_pos,h.frequency_cap.trans hp⟩

lemma lower_profile_zero (W : ℝ → ℂ) (a : ℝ) (ha : 0 < a)
    (h : ∀ x, W x ≠ 0 → a ≤ x) : W 0 = 0 := by
  by_contra hn
  exact (not_le_of_gt ha) (h 0 hn)

theorem main_lower_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (l a : ℝ) (hl : 0 < l) (ha : 0 < a)
    (s : Input ι) (hc : Fintype.card ι ≤ N) (hs : l ≤ s.lower)
    (hW₁ : ∀ x, s.W₁ x ≠ 0 → a ≤ x) (hW₂ : ∀ x, s.W₂ x ≠ 0 → a ≤ x)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    ∀ I : Ideal O, coefficient (child s C R B τ t) (R*C) seed I ≠ 0 →
      lowerFactor N l a * volume (child s C R B τ t) ≤ (I.absNorm : ℝ) := by
  intro I hI
  exact actual_lower_support N l a hl ha (child s C R B τ t)
    ((live_card_le B.val).trans hc) hs hW₁ hW₂ (R*C) seed I hI

theorem error_lower_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (l a : ℝ) (hl : 0 < l) (ha : 0 < a)
    (s : Input ι) (hc : Fintype.card ι ≤ N) (hs : l ≤ s.lower)
    (hW₁ : ∀ x, s.W₁ x ≠ 0 → a ≤ x) (hW₂ : ∀ x, s.W₂ x ≠ 0 → a ≤ x)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    ∀ I : Ideal O, coefficient (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed I ≠ 0 →
      lowerFactor N l a * volume (errorInput s C R B τ t Q k Bp υ v) ≤ (I.absNorm : ℝ) := by
  intro I hI
  exact actual_lower_support N l a hl ha (errorInput s C R B τ t Q k Bp υ v)
    ((live_card_le Bp.val).trans ((live_card_le B.val).trans hc))
    hs hW₁ hW₂ ((R*C)*(Q^k)) seed I hI

theorem eventual_parent_radius (N : ℕ) (b b₁ b₂ : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s →
      ∀ A : ℝ, volume s ≤ Z^A → sourceRadius s ≤ Z^(A+1) := by
  let G := b^N*b₁*b₂
  have hG : 1 ≤ G := by
    have hp : 1 ≤ b^N := one_le_pow₀ hb
    dsimp [G]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hp hb₁) hb₂
  filter_upwards [eventual_geometry G 1 hG (by norm_num)] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro ι _ _ s hc he A hV
  have hr := (radius_bound N b b₁ b₂ hb hb₁ hb₂ s hc he).2
  have hg : G ≤ Z := by simpa only [Real.rpow_one] using hZ.2.1
  apply hr.trans
  calc
    G * volume s ≤ Z * Z^A := mul_le_mul hg hV (volume_pos s).le (zero_lt_one.trans hZ.1).le
    _ = Z^(A+1) := by rw [Real.rpow_add_one (zero_lt_one.trans hZ.1).ne']; ring

theorem eventually_main_packet (N : ℕ) (b b₁ b₂ l a A P : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hl : 0 < l) (ha : 0 < a) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s → l ≤ s.lower →
      (∀ x, s.W₁ x ≠ 0 → a ≤ x) → (∀ x, s.W₂ x ≠ 0 → a ≤ x) →
      ∀ κ : ℝ, 1/6 ≤ κ → (∀ i, 1 ≤ s.P i) →
      length Z s.X₁ + length Z s.X₂ + 6*κ*(∑ i, Real.logb Z (s.P i)) ≤ A →
      (s.η.modulus.absNorm : ℝ) ≤ Z^A →
      ∀ R seed : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z^P → Squarefree seed →
      ∀ C D : Ideal O, ∀ hC : Supported C, ∀ hD : Supported D,
      (C,D) ∈ CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed))) →
      ∀ E : Finset (CommonIndex C D), ∀ ξ₁ ξ₂ : RayCharacter,
      ∀ F : FixedPair s.η C D hC E ξ₁ ξ₂, ∀ τ : Character, τ = F.left ∨ τ = F.right →
      ∀ K Csec Tsec σ ξ reserve : ℝ, 0 < K → 0 < Csec → 0 ≤ σ → 0 ≤ ξ → ξ ≤ 1 →
      0 ≤ reserve →
      Tsec ≤ Csec * firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s) →
      ∀ rows : Finset O, ∀ W : 𝓢(ℝ,ℂ), ∀ n : Fin 4 → ℤ,
      Retained (frequencyRadius Tsec Z ξ) (n 1) →
      block s.η (fixedBadMask*idealGenerator R) 1 s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
        C D hC hD E rows W (fun _ => logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0 →
      ∀ side : Bool, ∀ B : actualAllocations s.pools (columnIdeal C D side), ∀ t : ℝ,
      frozenCoefficient B.val (columnIdeal C D side) R s.ν s.W s.P ≠ 0 →
      let Km := columnMainRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side
      Ready (child s (columnIdeal C D side) R B τ t) (R*columnIdeal C D side) Km Z ξ (readyBudget A P) ∧
      (∀ I : Ideal O, coefficient (child s (columnIdeal C D side) R B τ t) (R*columnIdeal C D side) seed I ≠ 0 →
        lowerFactor N l a * volume (child s (columnIdeal C D side) R B τ t) ≤ (I.absNorm : ℝ)) := by
  filter_upwards [eventually_common_ready N b b₁ b₂ 1 hb hb₁ hb₂ (by norm_num),
    eventual_parent_radius N b b₁ b₂ hb hb₁ hb₂,
    eventually_caps 1 (by norm_num)] with Z hready hradius hchars
  refine ⟨hready.1, ?_⟩
  intro ι _ _ s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F τ hτ K Csec Tsec σ ξ reserve hK hCsec hσ hξ hξ1
    hreserve hsec rows W n hn hblock side B t hB
  dsimp only
  have hz := hready.1
  have hV := original_volume_cap s Z κ A hz hκ hPs hcapacity
  have hH := hradius.2 s hc he A hV
  have hz₁ := lower_profile_zero s.W₁ a ha hW₁
  have hz₂ := lower_profile_zero s.W₂ a ha hW₂
  have hcdata := actual_common_gates s R seed hseed hz₁ hz₂ C D hlabel
  have hCN := hcdata.2.2.2.2.2.1.trans hH
  have hJN : ((columnIdeal C D side).absNorm : ℝ) ≤ Z^(A+1) := by
    cases side
    · exact hCN
    · exact hcdata.2.2.2.2.2.2.trans hH
  have ht := hchars.2 s.η C D hC E ξ₁ ξ₂ F A (A+1) hη hCN
  have htau : (τ.modulus.absNorm : ℝ) ≤ Z^(3*A+3) := by
    have hx : (τ.modulus.absNorm : ℝ) ≤ Z^(A+2*(A+1)+1) := by
      rcases hτ with rfl | rfl
      · exact ht.1
      · exact ht.2.1
    simpa only [show A+2*(A+1)+1 = 3*A+3 by ring] using hx
  have hE : Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E} ≠ 0 := by
    exact Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
  have hne := first_block_active_rows_nonempty s.η (fixedBadMask*idealGenerator R) 1 s.t
    _ _ C D hC hD E rows W K n hblock
  have hrec := (active_row_reciprocals C D _ hE K (volume s) Z Csec Tsec ξ
    (Real.logb Z ((oppositeIdeal C D side).absNorm : ℝ))
    (Real.logb Z ((columnIdeal C D side).absNorm : ℝ)) σ reserve
    hK (volume_pos s) hz hCsec hσ hreserve hsec rows n hn hne 1 1).1
  have hKm : 0 < columnMainRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side := by
    unfold columnMainRadius mainCommonRadius
    positivity
  have hKmInv : (columnMainRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side)⁻¹ ≤ Z^(0 : ℝ) := by
    simpa only [columnMainRadius,nominalLog,Real.rpow_zero] using hrec
  have hr := hready.2 s hc he (columnIdeal C D side) R B τ t hR hB _ A 0 P (A+1) (3*A+3) ξ
    hKm hξ hV hKmInv hRN hJN htau
  exact ⟨ready_mono _ _ _ Z ξ _ _ hz.le (common_exponent_le A P ξ hA hP hξ1) hr,
    main_lower_support N l a hl ha s hc hs hW₁ hW₂ (columnIdeal C D side) R seed B τ t⟩

theorem eventually_error_packet (N : ℕ) (b b₁ b₂ l a A P : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hl : 0 < l) (ha : 0 < a) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s → l ≤ s.lower →
      (∀ x, s.W₁ x ≠ 0 → a ≤ x) → (∀ x, s.W₂ x ≠ 0 → a ≤ x) →
      ∀ κ : ℝ, 1/6 ≤ κ → (∀ i, 1 ≤ s.P i) →
      length Z s.X₁ + length Z s.X₂ + 6*κ*(∑ i, Real.logb Z (s.P i)) ≤ A →
      (s.η.modulus.absNorm : ℝ) ≤ Z^A →
      ∀ R seed : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z^P → Squarefree seed →
      ∀ C D : Ideal O, ∀ hC : Supported C, ∀ hD : Supported D,
      (C,D) ∈ CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed))) →
      ∀ E : Finset (CommonIndex C D), ∀ ξ₁ ξ₂ : RayCharacter,
      ∀ F : FixedPair s.η C D hC E ξ₁ ξ₂, ∀ τ : Character, τ = F.left ∨ τ = F.right →
      ∀ K Csec Tsec σ ξ reserve : ℝ, 0 < K → 0 < Csec → 0 ≤ σ → σ ≤ 1 →
      0 ≤ ξ → ξ ≤ 1 → 0 ≤ reserve →
      Tsec ≤ Csec * firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s) →
      ∀ rows : Finset O, ∀ W : 𝓢(ℝ,ℂ), ∀ n : Fin 4 → ℤ,
      Retained (frequencyRadius Tsec Z ξ) (n 1) →
      block s.η (fixedBadMask*idealGenerator R) 1 s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
        C D hC hD E rows W (fun _ => logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0 →
      ∀ side : Bool, ∀ B : actualAllocations s.pools (columnIdeal C D side), ∀ t : ℝ,
      frozenCoefficient B.val (columnIdeal C D side) R s.ν s.W s.P ≠ 0 →
      ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (Sbad : Finset (Ideal O)),
      fixedBadPrimes ⊆ Sbad →
      ∀ p ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^(σ/3))),
      ∀ k : ℕ, k = 1 ∨ k = 6 ∨ k = 7 →
      (∀ i, ∀ I ∈ (activeInput (child s (columnIdeal C D side) R B τ t)).slots i, IsCoprime (Ideal.span {p}) I) →
      ∀ Bp : actualAllocations (activeInput (child s (columnIdeal C D side) R B τ t)).pools ((Ideal.span {p})^k),
      ∀ (χ : RayCharacter) (υ : Character) (v : ℝ),
      υ.modulus.absNorm ≤ radicalBound (childCharacter τ χ) fixedBadMask p (errorMovingExponent (k-1)) →
      let d := errorInput s (columnIdeal C D side) R B τ t (Ideal.span {p}) k Bp υ v
      let Re := (R*columnIdeal C D side)*(Ideal.span {p})^k
      let Ke := columnErrorRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side p k
      ((∀ I : Ideal O, coefficient d Re seed I = 0) ∧ normalizedGaussSource d Re seed ballProfile Ke = 0) ∨
      (Ready d Re Ke Z ξ (readyBudget A P) ∧
        (∀ I : Ideal O, coefficient d Re seed I ≠ 0 →
          lowerFactor N l a * volume d ≤ (I.absNorm : ℝ))) := by
  filter_upwards [eventually_active_error_ready N b b₁ b₂ 1 hb hb₁ hb₂ (by norm_num),
    eventual_parent_radius N b b₁ b₂ hb hb₁ hb₂,
    eventually_caps 1 (by norm_num)] with Z hready hradius hchars
  refine ⟨hready.1, ?_⟩
  intro ι _ _ s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F τ hτ K Csec Tsec σ ξ reserve hK hCsec hσ hσ1
    hξ hξ1 hreserve hsec rows W n hn hblock side B t hB M _ H Sbad hbad p hp k _hk
    hslot Bp χ υ v hυ
  dsimp only
  let d := errorInput s (columnIdeal C D side) R B τ t (Ideal.span {p}) k Bp υ v
  let Re := (R*columnIdeal C D side)*(Ideal.span {p})^k
  let Ke := columnErrorRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side p k
  by_cases hdead : ∀ I : Ideal O, coefficient d Re seed I = 0
  · exact Or.inl ⟨hdead, normalized_zero d Re seed hdead ballProfile Ke⟩
  right
  have hlive : ∃ I : Ideal O, (original d Re seed).beta I ≠ 0 := by
    simpa only [original_beta,not_forall] using hdead
  have hz := hready.1
  have hV := original_volume_cap s Z κ A hz hκ hPs hcapacity
  have hH := hradius.2 s hc he A hV
  have hz₁ := lower_profile_zero s.W₁ a ha hW₁
  have hz₂ := lower_profile_zero s.W₂ a ha hW₂
  have hcdata := actual_common_gates s R seed hseed hz₁ hz₂ C D hlabel
  have hCN := hcdata.2.2.2.2.2.1.trans hH
  have hJN : ((columnIdeal C D side).absNorm : ℝ) ≤ Z^(A+1) := by
    cases side
    · exact hCN
    · exact hcdata.2.2.2.2.2.2.trans hH
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(σ/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(σ/3)) Q hQ).2) p hp
  have hp0 : p ≠ 0 := hd.1.ne_zero
  have hQ : Ideal.span {p} ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hp0
  have hpupper := (pool_prime_log_range M H Sbad hbad Z σ hz p hp).2
  have hPN : ((Ideal.span {p}).absNorm : ℝ) ≤ Z^(σ/3) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hz.le hpupper
    rwa [Real.rpow_logb (zero_lt_one.trans hz) (ne_of_gt hz) (normValue_pos p hp0)] at hh
  have ht := hchars.2 s.η C D hC E ξ₁ ξ₂ F A (A+1) hη hCN
  have hv : (υ.modulus.absNorm : ℝ) ≤ Z^(3*A+3+σ/3) := by
    have hh := ht.2.2 τ υ hτ χ p hp0 (errorMovingExponent (k-1)) (σ/3) hυ hPN
    simpa only [show A+2*(A+1)+σ/3+1 = 3*A+3+σ/3 by ring] using hh
  have hE : Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E} ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
  have hne := first_block_active_rows_nonempty s.η (fixedBadMask*idealGenerator R) 1 s.t
    _ _ C D hC hD E rows W K n hblock
  have hrec := (active_row_reciprocals C D _ hE K (volume s) Z Csec Tsec ξ
    (Real.logb Z ((oppositeIdeal C D side).absNorm : ℝ))
    (Real.logb Z ((columnIdeal C D side).absNorm : ℝ)) σ reserve
    hK (volume_pos s) hz hCsec hσ hreserve hsec rows n hn hne p k).2
  have hKe : 0 < Ke := by
    dsimp [Ke,columnErrorRadius,errorCommonRadius]
    positivity
  have hKeInv : Ke⁻¹ ≤ Z^(0 : ℝ) := by
    simpa only [Ke,columnErrorRadius,nominalLog,Real.rpow_zero] using hrec
  have hr := hready.2 s hc he (columnIdeal C D side) R seed B τ t hR hB _ hQ k hslot Bp υ v Ke
    A 0 P (3*A+3+σ/3) ξ hKe hξ hz₁ hz₂ hV hKeInv hRN hv hlive
  exact ⟨ready_mono _ _ Ke Z ξ _ _ hz.le (error_exponent_le A P σ ξ hA hP hσ1 hξ1) hr,
    error_lower_support N l a hl ha s hc hs hW₁ hW₂ (columnIdeal C D side) R seed B τ t _ k Bp υ v⟩

end SevenEighths.CenteredMomentEnergyFirstLiveAdmission

end

end OAI

end Source1891

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstTwoSeedAdmission.lean; sha256: a27833627a10b0422bd1ca8736258c9d30eabe13cfcac91834142a3597d94d5d -/
section Source1892
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstTwoSeedAdmission
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open ActualEisensteinCubic CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstSecondInputGates CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplifiedRadiusLower CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAnnularInput CenteredMomentSectorLocalization
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceConductorCaps
open CenteredMomentEnergyInputParentCapacity CenteredMomentEnergyBands
open CenteredMomentEnergyAmplifiedChildWidth CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentActiveSource
open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CompletedGauss RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentRowNorm
open CenteredMomentEnergyFirstLiveAdmission
local notation "O" => HeckeFamily.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem eventually_main_packet (N : ℕ) (b b₁ b₂ l a A P : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hl : 0 < l) (ha : 0 < a) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s → l ≤ s.lower →
      (∀ x, s.W₁ x ≠ 0 → a ≤ x) → (∀ x, s.W₂ x ≠ 0 → a ≤ x) →
      ∀ κ : ℝ, 1/6 ≤ κ → (∀ i, 1 ≤ s.P i) →
      length Z s.X₁ + length Z s.X₂ + 6*κ*(∑ i, Real.logb Z (s.P i)) ≤ A →
      (s.η.modulus.absNorm : ℝ) ≤ Z^A →
      ∀ R seed0 : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z^P → Squarefree seed0 →
      ∀ C D : Ideal O, ∀ hC : Supported C, ∀ hD : Supported D,
      (C,D) ∈ CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)))
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0))) →
      ∀ E : Finset (CommonIndex C D), ∀ ξ₁ ξ₂ : RayCharacter,
      ∀ F : FixedPair s.η C D hC E ξ₁ ξ₂, ∀ τ : Character, τ = F.left ∨ τ = F.right →
      ∀ K Csec Tsec σ ξ reserve : ℝ, 0 < K → 0 < Csec → 0 ≤ σ → 0 ≤ ξ → ξ ≤ 1 →
      0 ≤ reserve →
      Tsec ≤ Csec * firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s) →
      ∀ rows : Finset O, ∀ W : 𝓢(ℝ,ℂ), ∀ n : Fin 4 → ℤ,
      Retained (frequencyRadius Tsec Z ξ) (n 1) →
      block s.η (fixedBadMask*idealGenerator R) 1 s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)
        C D hC hD E rows W (fun _ => logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0 →
      ∀ side : Bool, ∀ B : actualAllocations s.pools (columnIdeal C D side), ∀ t : ℝ, ∀ innerL : Ideal O,
      frozenCoefficient B.val (columnIdeal C D side) R s.ν s.W s.P ≠ 0 →
      let Km := columnMainRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side
      Ready (child s (columnIdeal C D side) R B τ t) (R*columnIdeal C D side) Km Z ξ (readyBudget A P) ∧
      (∀ I : Ideal O, coefficient (child s (columnIdeal C D side) R B τ t) (R*columnIdeal C D side) innerL I ≠ 0 →
        lowerFactor N l a * volume (child s (columnIdeal C D side) R B τ t) ≤ (I.absNorm : ℝ)) := by
  filter_upwards [CenteredMomentEnergyFirstLiveAdmission.eventually_main_packet
    N b b₁ b₂ l a A P hb hb₁ hb₂ hl ha hA hP] with Z hz
  refine ⟨hz.1, ?_⟩
  intro ι _ _ s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed0 hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F τ hτ K Csec Tsec σ ξ reserve hK hCsec hσ hξ hξ1
    hreserve hsec rows W n hn hblock side B t innerL hB
  dsimp only
  have hm := hz.2 s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed0 hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F τ hτ K Csec Tsec σ ξ reserve hK hCsec hσ hξ hξ1
    hreserve hsec rows W n hn hblock side B t hB
  exact ⟨hm.1, main_lower_support N l a hl ha s hc hs hW₁ hW₂
    (columnIdeal C D side) R innerL B τ t⟩

theorem eventually_error_packet (N : ℕ) (b b₁ b₂ l a A P : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hl : 0 < l) (ha : 0 < a) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s → l ≤ s.lower →
      (∀ x, s.W₁ x ≠ 0 → a ≤ x) → (∀ x, s.W₂ x ≠ 0 → a ≤ x) →
      ∀ κ : ℝ, 1/6 ≤ κ → (∀ i, 1 ≤ s.P i) →
      length Z s.X₁ + length Z s.X₂ + 6*κ*(∑ i, Real.logb Z (s.P i)) ≤ A →
      (s.η.modulus.absNorm : ℝ) ≤ Z^A →
      ∀ R seed0 : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z^P → Squarefree seed0 →
      ∀ C D : Ideal O, ∀ hC : Supported C, ∀ hD : Supported D,
      (C,D) ∈ CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)))
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0))) →
      ∀ E : Finset (CommonIndex C D), ∀ ξ₁ ξ₂ : RayCharacter,
      ∀ F : FixedPair s.η C D hC E ξ₁ ξ₂, ∀ τ : Character, τ = F.left ∨ τ = F.right →
      ∀ K Csec Tsec σ ξ reserve : ℝ, 0 < K → 0 < Csec → 0 ≤ σ → σ ≤ 1 →
      0 ≤ ξ → ξ ≤ 1 → 0 ≤ reserve →
      Tsec ≤ Csec * firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s) →
      ∀ rows : Finset O, ∀ W : 𝓢(ℝ,ℂ), ∀ n : Fin 4 → ℤ,
      Retained (frequencyRadius Tsec Z ξ) (n 1) →
      block s.η (fixedBadMask*idealGenerator R) 1 s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)
        C D hC hD E rows W (fun _ => logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0 →
      ∀ side : Bool, ∀ B : actualAllocations s.pools (columnIdeal C D side), ∀ t : ℝ, ∀ innerL : Ideal O,
      frozenCoefficient B.val (columnIdeal C D side) R s.ν s.W s.P ≠ 0 →
      ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (Sbad : Finset (Ideal O)),
      fixedBadPrimes ⊆ Sbad →
      ∀ p ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^(σ/3))),
      ∀ k : ℕ, k = 1 ∨ k = 6 ∨ k = 7 →
      (∀ i, ∀ I ∈ (activeInput (child s (columnIdeal C D side) R B τ t)).slots i, IsCoprime (Ideal.span {p}) I) →
      ∀ Bp : actualAllocations (activeInput (child s (columnIdeal C D side) R B τ t)).pools ((Ideal.span {p})^k),
      ∀ (χ : RayCharacter) (υ : Character) (v : ℝ),
      υ.modulus.absNorm ≤ radicalBound (childCharacter τ χ) fixedBadMask p (errorMovingExponent (k-1)) →
      let d := errorInput s (columnIdeal C D side) R B τ t (Ideal.span {p}) k Bp υ v
      let Re := (R*columnIdeal C D side)*(Ideal.span {p})^k
      let Ke := columnErrorRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side p k
      ((∀ I : Ideal O, coefficient d Re innerL I = 0) ∧ normalizedGaussSource d Re innerL ballProfile Ke = 0) ∨
      (Ready d Re Ke Z ξ (readyBudget A P) ∧
        (∀ I : Ideal O, coefficient d Re innerL I ≠ 0 →
          lowerFactor N l a * volume d ≤ (I.absNorm : ℝ))) := by
  filter_upwards [eventually_active_error_ready N b b₁ b₂ 1 hb hb₁ hb₂ (by norm_num),
    eventual_parent_radius N b b₁ b₂ hb hb₁ hb₂,
    eventually_caps 1 (by norm_num)] with Z hready hradius hchars
  refine ⟨hready.1, ?_⟩
  intro ι _ _ s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed0 hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F τ hτ K Csec Tsec σ ξ reserve hK hCsec hσ hσ1
    hξ hξ1 hreserve hsec rows W n hn hblock side B t innerL hB M _ H Sbad hbad p hp k _hk
    hslot Bp χ υ v hυ
  dsimp only
  let d := errorInput s (columnIdeal C D side) R B τ t (Ideal.span {p}) k Bp υ v
  let Re := (R*columnIdeal C D side)*(Ideal.span {p})^k
  let Ke := columnErrorRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side p k
  by_cases hdead : ∀ I : Ideal O, coefficient d Re innerL I = 0
  · exact Or.inl ⟨hdead, normalized_zero d Re innerL hdead ballProfile Ke⟩
  right
  have hlive : ∃ I : Ideal O, (original d Re innerL).beta I ≠ 0 := by
    simpa only [original_beta,not_forall] using hdead
  have hz := hready.1
  have hV := original_volume_cap s Z κ A hz hκ hPs hcapacity
  have hH := hradius.2 s hc he A hV
  have hz₁ := lower_profile_zero s.W₁ a ha hW₁
  have hz₂ := lower_profile_zero s.W₂ a ha hW₂
  have hcdata := actual_common_gates s R seed0 hseed hz₁ hz₂ C D hlabel
  have hCN := hcdata.2.2.2.2.2.1.trans hH
  have hJN : ((columnIdeal C D side).absNorm : ℝ) ≤ Z^(A+1) := by
    cases side
    · exact hCN
    · exact hcdata.2.2.2.2.2.2.trans hH
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(σ/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(σ/3)) Q hQ).2) p hp
  have hp0 : p ≠ 0 := hd.1.ne_zero
  have hQ : Ideal.span {p} ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hp0
  have hpupper := (pool_prime_log_range M H Sbad hbad Z σ hz p hp).2
  have hPN : ((Ideal.span {p}).absNorm : ℝ) ≤ Z^(σ/3) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hz.le hpupper
    rwa [Real.rpow_logb (zero_lt_one.trans hz) (ne_of_gt hz) (normValue_pos p hp0)] at hh
  have ht := hchars.2 s.η C D hC E ξ₁ ξ₂ F A (A+1) hη hCN
  have hv : (υ.modulus.absNorm : ℝ) ≤ Z^(3*A+3+σ/3) := by
    have hh := ht.2.2 τ υ hτ χ p hp0 (errorMovingExponent (k-1)) (σ/3) hυ hPN
    simpa only [show A+2*(A+1)+σ/3+1 = 3*A+3+σ/3 by ring] using hh
  have hE : Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E} ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
  have hne := first_block_active_rows_nonempty s.η (fixedBadMask*idealGenerator R) 1 s.t
    _ _ C D hC hD E rows W K n hblock
  have hrec := (active_row_reciprocals C D _ hE K (volume s) Z Csec Tsec ξ
    (Real.logb Z ((oppositeIdeal C D side).absNorm : ℝ))
    (Real.logb Z ((columnIdeal C D side).absNorm : ℝ)) σ reserve
    hK (volume_pos s) hz hCsec hσ hreserve hsec rows n hn hne p k).2
  have hKe : 0 < Ke := by
    dsimp [Ke,columnErrorRadius,errorCommonRadius]
    positivity
  have hKeInv : Ke⁻¹ ≤ Z^(0 : ℝ) := by
    simpa only [Ke,columnErrorRadius,nominalLog,Real.rpow_zero] using hrec
  have hr := hready.2 s hc he (columnIdeal C D side) R innerL B τ t hR hB _ hQ k hslot Bp υ v Ke
    A 0 P (3*A+3+σ/3) ξ hKe hξ hz₁ hz₂ hV hKeInv hRN hv hlive
  exact ⟨ready_mono _ _ Ke Z ξ _ _ hz.le (error_exponent_le A P σ ξ hA hP hσ1 hξ1) hr,
    error_lower_support N l a hl ha s hc hs hW₁ hW₂ (columnIdeal C D side) R innerL B τ t _ k Bp υ v⟩

end SevenEighths.CenteredMomentEnergyFirstTwoSeedAdmission

end

end OAI

end Source1892

/- Original source: OAI/NumberTheory/DirichletL/Moments/RelativeCapacityRemoval.lean; sha256: 21f0c7cbd78787d7e7f70f69e933d8f1705f2f250d17015ae1e42422f7e89169 -/
section Source1893
namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff Topology
namespace SevenEighths.CenteredMomentRelativeCapacityRemoval
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily Filter
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem relative_slots_uniform {ι:Type*}[Fintype ι]
    (W:ι→ℝ→ℂ)(a b:ι→ℝ)(ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i))(hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot loss lo hi κ:ℝ)(hLm:0≤Lmod)(hLs:0≤Lslot)(hloss:0<loss)
    (hbeta:(51/100:ℝ)≤beta)(hκ:2*beta-1≤κ):
    ∃degree:ℕ,∃C:ℝ,1≤C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀i:ι,∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q:Ideal O,Q≤M → Q≤(ν i).modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀σ t v V:ℝ,lo≤σ → σ≤hi → 0≤V → |v|≤V →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H (b i) P)
        (fun I=>idealCoeff (ν i) I*annularWeight (W i) P σ v I) t P‖^2≤
        C*(1+|t|+V)^degree*Z^loss*P^κ := by
  choose degree C hC hb using fun i=>natural_character_slot_bound M H hH (W i) (a i) (b i)
    (ha i) (hWs i) (hW i) Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  let Ctotal:ℝ:=1+∑i,C i
  have hCtotal:1≤Ctotal:=by
    have hsum:=Finset.sum_nonneg (fun i (_:i∈Finset.univ)=>(hC i).le)
    dsimp [Ctotal];linarith
  have hCi (i:ι):C i≤Ctotal:=by
    have hsum:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hC j).le) (Finset.mem_univ i)
    dsimp [Ctotal];linarith
  refine ⟨∑i,degree i,Ctotal,hCtotal,?_⟩
  intro ν
  have hev:∀ᶠZ:ℝ in atTop,∀i:ι,_ := Filter.eventually_all.mpr (fun i=>hb i (ν i))
  obtain ⟨Zbase,hbase⟩:=eventually_atTop.mp hev
  refine ⟨max 2 Zbase,lt_max_of_lt_left (by norm_num),?_⟩
  intro i Z P hZ hP hPcap η z hz F hcond Q hQM hQν hex σ t v V hσ hσhi hV hv
  have hZ0:Zbase≤Z:=(le_max_right _ _).trans hZ
  have hZp:0<Z:=lt_of_lt_of_le (by norm_num:0<(2:ℝ)) ((le_max_left _ _).trans hZ)
  refine (hbase Z hZ0 i P hP hPcap η z hz F hcond Q hQM hQν hex σ t v hσ hσhi).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
  apply mul_le_mul (hCi i) _ (by positivity) (zero_le_one.trans hCtotal)
  calc
    _≤(1+|t|+V)^(degree i):=pow_le_pow_left₀ (by positivity) (by linarith) _
    _≤_:=pow_le_pow_right₀ (by linarith [abs_nonneg t])
      (Finset.single_le_sum (fun j _=>Nat.zero_le _) (Finset.mem_univ i))

theorem actual_relative_capacity_removal {ι:Type*}[Fintype ι][DecidableEq ι]
    (W:ι→ℝ→ℂ)(a b:ι→ℝ)(ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i))(hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot ε lo hi κ:ℝ)(hLm:0≤Lmod)(hLs:0≤Lslot)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤beta)(hκ:2*beta-1≤κ):
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q:Ideal O,Q≤M → (∀i,Q≤(ν i).modulus) → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>idealCoeff (ν i) I*annularWeight (W i) (P i) (σ i) (freq i) I
      ‖selectedProduct J η fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂‖^2≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          ‖selectedProduct (J\R) η fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂‖^2 := by
  let N:=Fintype.card ι
  let loss:=ε/((N:ℝ)+1)
  have hloss:0<loss:=div_pos hε (by positivity)
  obtain ⟨degree,C,hC,hbound⟩:=relative_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  have hκpos:0<κ:=by linarith
  refine ⟨degree*N,C^N,pow_pos (zero_lt_one.trans_le hC) _,?_⟩
  intro ν
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound ν
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  let excess:=CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ
  obtain ⟨R,hR,hRsum,hpay,hcost⟩:=whole_removal J w excess κ mesh (le_max_right _ _) hκpos hmesh
    (fun i _=>hw i) (fun i _=>hwm i)
  refine ⟨R,hR,CenteredMomentLiveCapacity.remaining_capacity J R hR w n₁ n₂ width κ hpay,hcost,?_⟩
  intro Z hZ η z hz F hcond Q hQM hQν hex σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂
  dsimp only
  have hZ1:1≤Z:=hZ₀.le.trans hZ
  have hZp:0<Z:=zero_lt_one.trans_le hZ1
  let B:=C*(1+|t|+V)^degree*Z^loss
  have hB:1≤B:=by
    have ht:1≤(1+|t|+V)^degree:=one_le_pow₀ (by linarith [abs_nonneg t])
    have hz:1≤Z^loss:=Real.one_le_rpow hZ1 hloss.le
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC ht) hz
  have hs:∀i∈R,‖normalizedSlot η fixedBadMask 1 z (primePool M H (b i) (Z^(w i)))
      (fun I=>idealCoeff (ν i) I*annularWeight (W i) (Z^(w i)) (σ i) (freq i) I) t (Z^(w i))‖^2≤
      B*Z^(κ*w i) := by
    intro i hi
    have hb:=hbound i Z (Z^(w i)) hZ (Real.one_le_rpow hZ1 (hw i))
      (Real.rpow_le_rpow_of_exponent_le hZ1 (hwcap i)) η z hz F hcond Q hQM (hQν i) hex
      (σ i) t (freq i) V (hσ i) (hσhi i) hV (hfreq i)
    rw [←Real.rpow_mul hZp.le] at hb
    simpa only [B,mul_comm (w i) κ] using hb
  have he:=selectedProduct_energy_remove J R hR η fixedBadMask 1 z W₁ W₂
    (fun i=>primePool M H (b i) (Z^(w i)))
    (fun i I=>idealCoeff (ν i) I*annularWeight (W i) (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) t X₁ X₂ Z κ hZp w (fun _=>B) (fun i hi=>zero_le_one.trans hB) hs
  apply he.trans
  gcongr 1
  have hcard:R.card≤N:=Finset.card_le_univ R
  have hpow:(∏i∈R,B)≤B^N:=by
    rw [Finset.prod_const]
    exact pow_le_pow_right₀ hB hcard
  have hcostZ:Z^(κ*∑i∈R,w i)≤Z^(excess/6+κ*mesh):=
    Real.rpow_le_rpow_of_exponent_le hZ1 hcost
  have hsplit:B^N=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)):=by
    dsimp [B]
    rw [mul_pow,mul_pow,←pow_mul,←Real.rpow_natCast (Z^loss) N,←Real.rpow_mul hZp.le]
  have hlossN:loss*(N:ℝ)≤ε:=by
    dsimp [loss]
    have hden:0<(N:ℝ)+1:=by positivity
    have hh:ε/((N:ℝ)+1)*((N:ℝ)+1)=ε:=div_mul_cancel₀ _ hden.ne'
    nlinarith [hloss.le]
  calc
    _≤B^N*Z^(excess/6+κ*mesh):=mul_le_mul hpow hcostZ (Real.rpow_nonneg hZp.le _) (by positivity)
    _=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)+(excess/6+κ*mesh)):=by
      rw [hsplit,mul_assoc,←Real.rpow_add hZp]
    _≤_:=mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)) (by positivity)
  apply le_of_eq
  congr 3
  ext i
  simp

end SevenEighths.CenteredMomentRelativeCapacityRemoval

end

end OAI

end Source1893

/- Original source: OAI/NumberTheory/DirichletL/Energy/CapacityRemoval.lean; sha256: 228a8a2fba534a190e6b8573322f2f1e3b1784a408e15e5af4430698cb8e8ad9 -/
section Source1894
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCapacityRemoval
open HeckeFamily ConcreteTraceCRT CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot
open CenteredMomentSlotNormalization CenteredMomentRelativeCapacityRemoval
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentEnergyState
open CenteredExceptionalProfile CenteredMomentFixedRowMask
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem compact_radial_summable (f : O→ℂ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ))
    (K b : ℝ) (hK : 0<K) (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic b) :
    Summable (fun z : O=>if keep z then ‖f z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨N,hN⟩:=exists_nat_ge (b*K)
  apply summable_of_ne_finset_zero (s:=ShortDraftLatticeCount.rowNormBall N)
  intro z hz
  have hΦ : Φ (‖eisEmbedding z‖^2/K)=0 := by
    by_contra hn
    have hh : ‖eisEmbedding z‖^2≤(N:ℝ):=((div_le_iff₀ hK).mp (hs hn)).trans hN
    apply hz
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    exact_mod_cast (show ((Ideal.span {z}).absNorm:ℝ)≤N by
      rwa [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span])
  simp [hΦ]

omit [DecidableEq ι] in

theorem energy_support (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ S β P X₁ X₂
        (fun z=>keep z ∧ Φ (‖eisEmbedding z‖^2/K)≠0) Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  by_cases hk : keep z <;> by_cases hp : Φ (‖eisEmbedding z‖^2/K)=0 <;> simp [hk,hp]

omit [Fintype ι] in

theorem selected_eq_positive (J : Finset ι) (η : Character) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) (hX : 0≤X₁*X₂) (hP : ∀i,0≤P i) :
    selectedProduct J η m A z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ (fun i:J=>S i) (fun i:J=>β i)
        (fun i:J=>P i) t X₁ X₂ := by
  have hh:=selectedProduct_univ η m A z W₁ W₂
    (fun i:J=>S i) (fun i:J=>β i) (fun i:J=>P i) t X₁ X₂ hX (fun i=>hP i)
  have hp : (∏i:J,normalizedSlot η m A z (S i) (β i) t (P i))=
      ∏i∈J,normalizedSlot η m A z (S i) (β i) t (P i) :=
    Finset.prod_coe_sort J (fun i=>normalizedSlot η m A z (S i) (β i) t (P i))
  unfold selectedProduct at hh ⊢
  rw [hp] at hh
  exact hh

theorem unit_puncture_energy (η : Character) (t : ℝ) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (hz : ∀z,keep z→z≠0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 t W₁ W₂ S β P X₁ X₂ keep Φ K=
      energy η fixedBadMask 1 t W₁ W₂ S β P X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  by_cases hk : keep z
  · simp only [ite_eq_left hk]
    rw [natural_unit_mask_positive (naturalRow η z (hz z hk))]
  · simp only [ite_eq_right hk]

theorem eventual_state_conductor (bΦ Mcap : ℝ) (hb : 0≤bΦ) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.width≤Mcap → ∀z:O,∀hz:z≠0,
      s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)≠0 →
      ((naturalRow s.character z hz).character.modulus.absNorm:ℝ)≤Z^(Mcap+1) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop ((fixedConductorFactor:ℝ)*bΦ)] with Z hZ hF
  refine ⟨hZ,?_⟩
  intro Bmask s hwidth z hz hΦ
  have hn : ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^s.rowWidth := by
    rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←s.scale_eq]
    exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hΦ)
  have he:=(naturalRow s.character z hz).modulus_power_bound Z s.characterWidth s.rowWidth bΦ
    (zero_lt_one.trans hZ) hb s.modulus_bound hn
  have hm:Z^(s.characterWidth+s.rowWidth)≤Z^Mcap:=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by simpa [NaturalState.width,add_comm] using hwidth)
  apply he.trans
  calc
    _≤Z*Z^Mcap:=mul_le_mul hF hm (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      (zero_lt_one.trans hZ).le
    _=Z^(Mcap+1):=by rw [Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_one];ring

theorem eventual_row_conductor (bΦ Mrow : ℝ) (hb : 0≤bΦ) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.rowWidth≤Mrow → ∀q:ℝ,(s.character.modulus.absNorm:ℝ)≤Z^q →
      ∀z:O,∀hz:z≠0,s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)≠0 →
      ((naturalRow s.character z hz).character.modulus.absNorm:ℝ)≤Z^(Mrow+q+1) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop ((fixedConductorFactor:ℝ)*bΦ)] with Z hZ hF
  refine ⟨hZ,?_⟩
  intro Bmask s hrow q hq z hz hΦ
  have hn : ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^s.rowWidth := by
    rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←s.scale_eq]
    exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hΦ)
  have he:=(naturalRow s.character z hz).modulus_power_bound Z q s.rowWidth bΦ
    (zero_lt_one.trans hZ) hb hq hn
  have hm:Z^(q+s.rowWidth)≤Z^(Mrow+q):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply he.trans
  calc
    _≤Z*Z^(Mrow+q):=mul_le_mul hF hm (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      (zero_lt_one.trans hZ).le
    _=Z^(Mrow+q+1):=by
      conv_rhs => rw [Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_one]
      ring

lemma state_unit_nonexceptional {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ)
    (hpuncture : s.puncture=1) (Q : Ideal O) (hQ : s.fixedModulus=Q)
    (z : O) (hk : s.radial.keep z) : ¬FixedInducingRow s.character Q fixedBadMask 1 z := by
  intro hh
  apply s.nonexceptional z hk
  rw [hQ,hpuncture]
  exact (fixedInducingRow_mul_mask_iff s.character Q fixedBadMask
    (ConcretePrimeRowBridge.idealGenerator 1) 1 z fixedBadMask_ne_zero
    (ConcretePrimeRowBridge.idealGenerator_ne_zero 1 one_ne_zero) one_ne_zero (s.row_ne_zero z hk)
    (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hh

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
include hH

theorem actual_state_capacity_removal
    (W : ι→ℝ→ℂ) (a b : ι→ℝ) (ha : ∀i,0<a i)
    (hWs : ∀i,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hW : ∀i,ContDiff ℝ ∞ (W i))
    (Mrow bΦ Lmod Lslot ε lo hi κ : ℝ) (hbΦ : 0≤bΦ)
    (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.puncture=1 → s.rowWidth≤Mrow → ∀q:ℝ,
      (s.character.modulus.absNorm:ℝ)≤Z^q → Mrow+q+1≤Lmod →
    ∀Q:Ideal O,s.fixedModulus=Q → Q≤M → (∀i,Q≤(ν i).modulus) →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),0<X₁ → 0<X₂ →
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
      energy s.character s.mask 1 t W₁ W₂ (fun i:J=>S i) (fun i:J=>coeff i)
        (fun i:J=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          energy s.character s.mask 1 t W₁ W₂ (fun i:↥(J\R)=>S i) (fun i:↥(J\R)=>coeff i)
            (fun i:↥(J\R)=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  obtain ⟨degree,C,hC,hbound⟩:=actual_relative_capacity_removal M H hH W a b ha hWs hW
    Lmod Lslot ε lo hi κ hLm hLs hε hbeta hκ
  obtain ⟨Zsupport,hsupport⟩:=eventually_atTop.mp (eventual_row_conductor bΦ Mrow hbΦ)
  refine ⟨degree,C,hC,?_⟩
  intro ν
  obtain ⟨Zbase,hZbase,hbound⟩:=hbound ν
  refine ⟨max Zbase Zsupport,lt_of_lt_of_le hZbase (le_max_left _ _),?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hcapacity,hcost,hpoint⟩:=hbound J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hcapacity,hcost,?_⟩
  intro Z hZ Bmask s hpuncture hrow q hmod hLmod Q hQ hQM hQν σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂ hX₁ hX₂
  dsimp only
  have hZbase' : Zbase≤Z:=(le_max_left _ _).trans hZ
  have hs:=(hsupport Z ((le_max_right _ _).trans hZ))
  have hZpos:0<Z:=zero_lt_one.trans hs.1
  have hscale (i:ι) : 0≤Z^(w i):=Real.rpow_nonneg hZpos.le _
  let P:=fun i=>Z^(w i)
  let S:=fun i=>primePool M H (b i) (P i)
  let coeff:=fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
  let cost:=C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)
  have hmask:s.mask=fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1:=by rw [NaturalState.mask,hpuncture]
  rw [hmask,unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero,
    unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero]
  change energy s.character fixedBadMask 1 t W₁ W₂ (fun i:J=>S i) (fun i:J=>coeff i)
    (fun i:J=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
    cost*energy s.character fixedBadMask 1 t W₁ W₂ (fun i:↥(J\R)=>S i) (fun i:↥(J\R)=>coeff i)
    (fun i:↥(J\R)=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale
  have hsum (T:Finset ι):=compact_radial_summable
    (fun z=>positiveSlotRow s.character fixedBadMask 1 z W₁ W₂ (fun i:T=>S i)
      (fun i:T=>coeff i) (fun i:T=>P i) t X₁ X₂)
    s.radial.keep s.radial.profile s.radial.scale bΦ s.radial.scale_pos s.radial_support
  unfold energy
  rw [←tsum_mul_left]
  apply (hsum J).tsum_le_tsum _ ((hsum (J\R)).mul_left cost)
  intro z
  by_cases hk:s.radial.keep z
  · simp only [ite_eq_left hk]
    by_cases hp:s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)=0
    · simp [hp]
    · have hz:=s.row_ne_zero z hk
      have hc:((naturalRow s.character z hz).character.modulus.absNorm:ℝ)≤Z^Lmod:=
        (hs.2 Bmask s hrow q hmod z hz hp).trans
          (Real.rpow_le_rpow_of_exponent_le hs.1.le hLmod)
      have hh:=hpoint Z hZbase' s.character z hz (naturalRow s.character z hz) hc
        Q hQM hQν (state_unit_nonexceptional s hpuncture Q hQ z hk)
        σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂
      dsimp only at hh
      rw [selected_eq_positive J s.character fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂ (mul_pos hX₁ hX₂).le hscale,
        selected_eq_positive (J\R) s.character fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂ (mul_pos hX₁ hX₂).le hscale] at hh
      exact (mul_le_mul_of_nonneg_right hh (s.radial.nonneg z)).trans_eq (by dsimp only [cost];ring)
  · simp only [ite_eq_right hk,mul_zero,le_refl]

theorem actual_relative_state_capacity_removal
    (W : ι→ℝ→ℂ) (a b : ι→ℝ) (ha : ∀i,0<a i)
    (hWs : ∀i,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hW : ∀i,ContDiff ℝ ∞ (W i))
    (Mrow bΦ Lmod Lslot ε lo hi κ : ℝ) (hbΦ : 0≤bΦ)
    (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀η₀:Character,∀θ:ι→RayQuotient.Characters M H,
    let ν:=fun i=>relativeCharacter M H hH η₀ (θ i);
    ∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.puncture=1 → s.rowWidth≤Mrow → ∀q:ℝ,
      (s.character.modulus.absNorm:ℝ)≤Z^q → Mrow+q+1≤Lmod →
    ∀Q:Ideal O,s.fixedModulus=internalQ Q η₀ → Q≤M →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),0<X₁ → 0<X₂ →
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
      energy s.character s.mask 1 t W₁ W₂ (fun i:J=>S i) (fun i:J=>coeff i)
        (fun i:J=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          energy s.character s.mask 1 t W₁ W₂ (fun i:↥(J\R)=>S i) (fun i:↥(J\R)=>coeff i)
            (fun i:↥(J\R)=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  obtain ⟨degree,C,hC,hbound⟩:=actual_state_capacity_removal M H hH W a b ha hWs hW
    Mrow bΦ Lmod Lslot ε lo hi κ hbΦ hLm hLs hε hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀ θ
  dsimp only
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound (fun i=>relativeCharacter M H hH η₀ (θ i))
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hcapacity,hcost,henergy⟩:=hbound J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hcapacity,hcost,?_⟩
  intro Z hZ Bmask s hpuncture hrow q hmod hLmod Q hQ hQM
  exact henergy Z hZ Bmask s hpuncture hrow q hmod hLmod (internalQ Q η₀) hQ
    (inf_le_left.trans hQM)
    (fun i=>relativeCharacter_fixedQ M H hH η₀ (θ i) (internalQ Q η₀)
      (inf_le_left.trans hQM) inf_le_right)

end SevenEighths.CenteredMomentEnergyCapacityRemoval

end

end OAI

end Source1894

/- Original source: OAI/NumberTheory/DirichletL/Energy/PaidBands.lean; sha256: 8f960a3cb424baaf0d737bdf18854dab3cb85cb87da38e6ed978bf5107bf1475 -/
section Source1895
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPaidBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentPrimeSlot CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] in
lemma remaining_energy_bound
    (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ)
    (hC₀:0≤C₀)(hC₁:0≤C₁)
    (hzero:ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀)
    (hpositive:PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C₁)
    (J R:Finset α)(θ:α→RayQuotient.Characters M H)(w σ v:α→ℝ)(t height:ℝ)
    (hw:∀i,0≤w i)(hwL:∀i,w i≤Lslot)(hσlo:∀i,lo≤σ i)(hσhi:∀i,σ i≤hi)
    (hheight:0≤height)(hv:∀i,|v i|≤height)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=internalQ Q η₀)(hs:s.width≤Mcap)
    (p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    (hcapacity:R=J ∨ length Z X₁+length Z X₂+6*κ*(∑i∈J\R,w i)≤s.width):
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:↥(J\R)=>primePool M H bslot (Z^(w i)))
      (fun (i:↥(J\R)) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:↥(J\R)=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      (C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε) := by
  have hd:=diagonalControl_nonneg s.radial.profile
  have hp:=sq_nonneg (p.control S)
  have hz:0≤Z^(s.width+ε):=Real.rpow_nonneg (zero_le_one.trans s.base_ge_one) _
  rcases hcapacity with hR|hcap
  · subst R
    let : IsEmpty ↥(J\J) := ⟨fun i=>by
      have hi:=Finset.mem_sdiff.mp i.property
      exact hi.2 hi.1⟩
    have he:=hzero s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
    have hid : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i:↥(J\J)=>primePool M H bslot (Z^(w i)))
        (fun (i:↥(J\J)) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i:↥(J\J)=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale =
        s.plainEnergy p t X₁ X₂ := by
      simp only [energy,positiveSlotRow,NaturalState.plainEnergy,
        Fintype.prod_empty,mul_one]
    rw [hid]
    apply he.trans
    simp only [Real.norm_eq_abs]
    have hpow:(1+|t|)^degree≤(1+|t|+height)^degree :=
      pow_le_pow_left₀ (by positivity) (by linarith) degree
    exact mul_le_mul_of_nonneg_right (mul_le_mul
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₁) hd) hp)
      hpow (by positivity) (mul_nonneg (mul_nonneg (add_nonneg hC₀ hC₁) hd) hp)) hz
  · have he:=hpositive (J\R) (fun i=>θ i) (fun i=>w i) (fun i=>σ i) (fun i=>v i)
      t height (fun i=>hw i) (fun i=>hwL i) (fun i=>hσlo i) (fun i=>hσhi i)
      hheight (fun i=>hv i) s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
      (by simpa only [Finset.sum_coe_sort] using hcap)
    apply he.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀) hd) hp)
        (pow_nonneg (by positivity) _)) hz

end SevenEighths.CenteredMomentEnergyPaidBands

end

end OAI

end Source1895

/- Original source: OAI/NumberTheory/DirichletL/Energy/PaidRemoval.lean; sha256: 556b5b47f65a04af7e5d016dbc68857a35decfce996e8000037a28da70b14eec -/
section Source1896
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyPaidRemoval
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyPaidBands CenteredMomentEnergyCapacityRemoval
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(a b Bmask L εchild:ℝ)(Q:Ideal O),Q≤M →
    ∀(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ),0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(J:Finset α)(w σ v:α→ℝ)(t height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|v i|≤height) →
    ∀s:NaturalState Z Bmask bΦ,s.puncture=1 → s.fixedModulus=internalQ Q η₀ → s.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:J=>primePool M H bslot (Z^(w i)))
      (fun (i:J) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:J=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      Cc*(C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^(dc+degree)*
        Z^(s.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess J w (length Z X₁) (length Z X₂) s.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hrem⟩:=actual_relative_state_capacity_removal (ι:=α) M H hH
    (fun _=>W) (fun _=>aslot) (fun _=>bslot) (fun _=>ha) (fun _=>hWs) (fun _=>hW)
    Mcap bΦ (2*Mcap+1) Lslot εremove lo hi κ hbΦ (by linarith) hLs hε hbeta hκ
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hrem⟩:=hrem η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    J w σ v t height mesh hmesh hw hwm hwL hσlo hσhi hheight hv s hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  obtain ⟨R,hR,hcapacity,hcost,henergy⟩:=hrem J w (length Z X₁) (length Z X₂)
    s.width mesh hmesh hw hwm hwL
  have hrow:s.rowWidth≤Mcap:=by
    have hc:=s.character_nonneg
    dsimp [NaturalState.width] at hs
    linarith
  have hq:Mcap+s.characterWidth+1≤2*Mcap+1:=by
    have hr:=s.row_nonneg
    dsimp [NaturalState.width] at hs
    linarith
  have he:=henergy Z hZ Bmask s hunit hrow s.characterWidth s.modulus_bound hq Q hQ hQM
    σ v t height hσlo hσhi hheight hv (p.profile 0) (p.profile 1) X₁ X₂ hX₁ hX₂
  dsimp only at he
  have hb:=remaining_energy_bound M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap εchild κ Z
    η₀ Q degree S C₀ C₁ hC₀ hC₁ hzero hpos J R θ w σ v t height
    hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  apply he.trans ((mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_)
  simp only [pow_add,Real.rpow_add hZp]
  ring

end SevenEighths.CenteredMomentEnergyPaidRemoval

end

end OAI

end Source1896

/- Original source: OAI/NumberTheory/DirichletL/Energy/AllocatedPaid.lean; sha256: 2a4e959b14915d80144401a0942d3d978938c52fcd8894517eacdc4d50671d3c -/
section Source1897
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyAllocatedPaid
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyPaidRemoval CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_allocated_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(a b Bmask L εchild:ℝ)(Q:Ideal O),Q≤M →
    ∀(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ),0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀st:NaturalState Z Bmask bΦ,st.puncture=1 → st.fixedModulus=internalQ Q η₀ → st.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    let d:=commonData (withHeight src st.character v) C R B
    energy st.character st.mask 1 0 (p.profile 0) (p.profile 1)
      (fun i:remaining src C B D alloc J=>d.slots i.val)
      (fun i:remaining src C B D alloc J=>CenteredMomentCommonMaskEnergy.heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining src C B D alloc J=>d.P i.val)
      X₁ X₂ st.radial.keep st.radial.profile st.radial.scale ≤
      Cc*(C₀+C₁)*diagonalControl st.radial.profile*(p.control S)^2*
        (1+(|v|+height))^(dc+degree)*
        Z^(st.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z X₁) (length Z X₂) st.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hbound⟩:=actual_paid_bands (α:=α) M H hH W aslot bslot Mcap bΦ Lslot
    εremove lo hi κ ha hWs hW hMcap hbΦ hLs hε hbeta hκ
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  dsimp only
  rw [common_energy hmatch st.character v C R B D alloc J st.mask 1
    (p.profile 0) (p.profile 1) X₁ X₂ st.radial.keep st.radial.profile st.radial.scale]
  have he:=hbound Z hZ a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    (originalImage src C B D alloc J) w σ (fun i=>v+freq i) 0 (|v|+height) mesh
    hmesh hw hwm hwL hσlo hσhi (add_nonneg (abs_nonneg _) hheight)
    (fun i=>(abs_add_le _ _).trans (add_le_add le_rfl (hfreq i)))
    st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  simpa only [abs_zero,add_zero] using he

end SevenEighths.CenteredMomentEnergyAllocatedPaid

end

end OAI

end Source1897

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonSectorColumn.lean; sha256: 228345d816415ee9aa49b3575692229a03b1d63acc6b47e0806b60184e010a61 -/
section Source1898
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonSectorColumn
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonLinearSource CenteredMomentSecondMaskedWindow
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource
open RayFourExpansion ActualEisensteinCubic CenteredMomentSourceRow CompletedGauss
local notation "O" => HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem actual_sector_column (s:Input ι)(η τ:Character)(χ:RayCharacter)(A:O)
    (C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(t:ℝ)(z:O)
    (hτ:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ) z=
      sourceColumn (withHeight s τ t) C hC R seed L z:=by
  dsimp only
  rw [funext (masked_divisor_coefficient η τ χ A C hC hτ _ _ L t)]
  apply (sector_rowPolynomial (finiteColumns (Fintype.piFinset s.pools))
    (fun I=>(if L∣I then finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I)
      else 0)*heightCoeff τ t I) C hC z).trans
  unfold sourceColumn
  dsimp only [withHeight,Input.pools]
  apply congrArg (fun c=>rowPolynomial Finset.univ
    (sourceGenerator (residualPool C hC.1 (finiteColumns (Fintype.piFinset (Sum.elim s.slots (fun j=>if j=0 then s.plain₁ else s.plain₂)))))) c z)
  funext I
  change (if IsCoprime C (I:Ideal O) then (if L∣(I:Ideal O) then _ else 0)*heightCoeff τ t I else 0)=
    (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then _ else 0)*heightCoeff τ t I
  split_ifs <;> simp_all

end SevenEighths.CenteredMomentCommonSectorColumn

end

end OAI

end Source1898

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalKernel.lean; sha256: f44fcda3492abc1f3e2bb1c9ec8e3c16124a6035abb810f30cd66719d3b17605 -/
section Source1899
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalKernel
open CenteredMomentSmooth CenteredMomentCauchy FourierBridge

theorem paired_row_triangle {κ : Type*} (rows : Finset κ)
    (w A B : κ → ℂ) (hw : ∀k∈rows,‖w k‖≤1) :
    ‖∑k∈rows,w k*A k*B k‖≤∑k∈rows,‖A k‖*‖B k‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro k hk
  rw [norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg _) (hw k hk)) (norm_nonneg _)

theorem common_density_pair {κ α β : Type*}
    (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (rows : Finset κ) (S : Finset α) (T : Finset β)
    (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
    (ρ x : κ → ℝ) (η : κ → ℂ)
    (hη : ∀ k ∈ rows, ‖η k‖ ≤ 1)
    (hV₀ : ∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) (hV₁ : ∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1)
    (E : ℝ) (_hE : 0 ≤ E) (J : ℕ)
    (henergy : ∀ t : ℝ,
      (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ *
        ‖rightColumn T (d k) (V 3) v t‖) ≤ E * (1 + ‖t‖) ^ J) :
    ‖∑ k ∈ rows, η k * ∫ t : ℝ, rowPhase V (ρ k) (x k) t *
      leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t‖ ≤
      E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖ := by
  have hrow (k : κ) (hk : k ∈ rows) (t : ℝ) : ‖η k * rowPhase V (ρ k) (x k) t‖ ≤ 1 := by
    rw [norm_mul, rowPhase, norm_mul, norm_mul, norm_mul, logPhase_norm, logPhase_norm, mul_one, mul_one]
    exact (mul_le_of_le_one_left (by positivity) (hη k hk)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hV₀ k hk)).trans (hV₁ k hk))
  have hpoint (t : ℝ) :
      ‖∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ ≤
        E * ((1 + ‖t‖) ^ J * ‖b t‖) := by
    have hs := paired_row_triangle rows (fun k => η k * rowPhase V (ρ k) (x k) t)
      (fun k => leftColumn S (c k) (V 2) u t) (fun k => rightColumn T (d k) (V 3) v t)
      (fun k hk => hrow k hk t)
    have he : (∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)) =
        (∑ k ∈ rows, (η k * rowPhase V (ρ k) (x k) t) *
          leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t) * b t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [he, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hs.trans (henergy t)) (norm_nonneg _)).trans_eq (by ring)
  have hi : Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) :=
    JointLogSeparation.weighted_schwartz_integrable b J
  calc
    _ = ‖∫ t : ℝ, ∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ := by
      congr 1
      rw [integral_finsetSum _ (fun k _ =>
        paired_columns_integrable b V (ρ k) (x k) S T (c k) (d k) u v (η k))]
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul]
    _ ≤ ∫ t : ℝ, E * ((1 + ‖t‖) ^ J * ‖b t‖) :=
      norm_integral_le_of_norm_le (hi.const_mul E) (Filter.Eventually.of_forall hpoint)
    _ = _ := integral_const_mul _ _

theorem whole_kernel_paired_row_estimate (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {κ α β : Type*} (rows : Finset κ) (S : Finset α) (T : Finset β)
        (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : κ → ℝ) (η : κ → ℂ),
      (∀ k ∈ rows, ‖η k‖ ≤ 1) →
      (∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) → (∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ, (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ *
        ‖rightColumn T (d k) (V 3) v t‖) ≤ E * (1 + ‖t‖) ^ J) →
      (1 + R) ^ A * ‖∑ k ∈ rows, η k *
        (∑ i ∈ S, ∑ j ∈ T, (c k i * star (d k j)) *
          wholeKernel W V R (ρ k) (x k) (u i) (v j))‖ ≤ C * E := by
  obtain ⟨C, hC, hs⟩ := whole_product_pair_separation W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR κ α β rows S T c d u v ρ x η hη hV₀ hV₁ E hE he
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  have hid (k : κ) := hb S T (c k) (d k) u v (ρ k) (x k)
  simp_rw [hid]
  have hcs := common_density_pair b V rows S T c d u v ρ x η hη hV₀ hV₁ E hE J he
  change (1 + R) ^ A * ‖∑ k ∈ rows, η k * ∫ t : ℝ,
    rowPhase V (ρ k) (x k) t * leftColumn S (c k) (V 2) u t *
      rightColumn T (d k) (V 3) v t * b t‖ ≤ _
  calc
    _ ≤ (1 + R) ^ A * (E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = E * ((1 + R) ^ A * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) := by ring
    _ ≤ E * C := mul_le_mul_of_nonneg_left hm hE
    _ = _ := mul_comm _ _

end SevenEighths.CenteredMomentExceptionalKernel

end

end OAI

end Source1899

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalWindowPair.lean; sha256: 5c5cf58f5b0fc0ba11a73a980c66adba7e9cb0db02bf8c4defa5941946711f8e -/
section Source1900
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalWindowPair
open CenteredMomentPlainWindowEnergy CenteredMomentRowNorm CenteredMomentSmooth
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem paired_integrals {κ:Type*}(rows:Finset κ)(f g:κ→ℝ→ℂ)
    (hf:∀z∈rows,Integrable (f z))(hg:∀z∈rows,Integrable (g z))
    (a b:ℝ→ℝ)(ha:Integrable a)(hb:Integrable b)
    (_ha0:∀u,0≤a u)(_hb0:∀v,0≤b v)(E:ℝ)(_hE:0≤E)
    (hpair:∀u v,∑z∈rows,‖f z u‖*‖g z v‖≤E*a u*b v):
    (∑z∈rows,‖∫u,f z u‖*‖∫v,g z v‖)≤E*(∫u,a u)*(∫v,b v):=by
  have hinner (u:ℝ):
      (∑z∈rows,‖f z u‖*‖∫v,g z v‖)≤E*a u*(∫v,b v):=by
    calc
      _≤∑z∈rows,‖f z u‖*(∫v,‖g z v‖):=
        Finset.sum_le_sum (fun z hz=>mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm _) (norm_nonneg _))
      _=∫v,∑z∈rows,‖f z u‖*‖g z v‖:=by
        rw [integral_finsetSum _ (fun z hz=>(hg z hz).norm.const_mul _)]
        simp only [integral_const_mul]
      _≤∫v,E*a u*b v:=integral_mono
        (integrable_finsetSum rows (fun z hz=>(hg z hz).norm.const_mul _))
        (hb.const_mul _) (fun v=>hpair u v)
      _=E*a u*(∫v,b v):=integral_const_mul _ _
  calc
    _≤∑z∈rows,(∫u,‖f z u‖)*‖∫v,g z v‖:=
      Finset.sum_le_sum (fun z hz=>mul_le_mul_of_nonneg_right
        (norm_integral_le_integral_norm _) (norm_nonneg _))
    _=∫u,∑z∈rows,‖f z u‖*‖∫v,g z v‖:=by
      rw [integral_finsetSum _ (fun z hz=>(hf z hz).norm.mul_const _)]
      simp only [integral_mul_const]
    _≤∫u,E*a u*(∫v,b v):=integral_mono
      (integrable_finsetSum rows (fun z hz=>(hf z hz).norm.mul_const _))
      ((ha.const_mul E).mul_const _) hinner
    _=E*(∫u,a u)*(∫v,b v):=by rw [integral_mul_const,integral_const_mul]

theorem plain_window_pair {α β:Type*}
    (rows:Finset O)(S:Finset α)(T:Finset β)(a:α→O)(b:β→O)
    (ha:∀i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (hb:∀j,CanonicalQuadraticSieve.Supported (Ideal.span {b j}))
    (c:α→ℂ)(d:β→ℂ)(τ₁ τ₂:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u v:ℝ,(∑z∈rows,
      ‖rowPolynomial S a (fun i=>c i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) z‖*
      ‖rowPolynomial T b (fun j=>d j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) z‖)≤
        E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):
    (∑z∈rows,
      ‖rowPolynomial S a (fun i=>c i*heightCoeff τ₁ t₁ (Ideal.span {a i})*
        columnPhase V₁ (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ₁) z‖*
      ‖rowPolynomial T b (fun j=>d j*heightCoeff τ₂ t₂ (Ideal.span {b j})*
        columnPhase V₂ (Real.log ((Ideal.absNorm (Ideal.span {b j}):ℝ)/Y)) θ₂) z‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫v:ℝ,(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖):=by
  let f:=fun z:O=>fun u:ℝ=>columnDensity V₁ hc₁ hs₁ u*logPhase (θ₁-u) (Real.log X)*
    rowPolynomial S a (fun i=>c i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) z
  let g:=fun z:O=>fun v:ℝ=>columnDensity V₂ hc₂ hs₂ v*logPhase (θ₂-v) (Real.log Y)*
    rowPolynomial T b (fun j=>d j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) z
  have hf (z:O):Integrable (f z):=plain_column_integrable S a ha c τ₁ t₁ θ₁ X hX V₁ hc₁ hs₁ z
  have hg (z:O):Integrable (g z):=plain_column_integrable T b hb d τ₂ t₂ θ₂ Y hY V₂ hc₂ hs₂ z
  have hh:=paired_integrals rows f g (fun z _=>hf z) (fun z _=>hg z)
    (fun u=>(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)
    (fun v=>(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖)
    (columnDensity_moments V₁ hc₁ hs₁ J₁) (columnDensity_moments V₂ hc₂ hs₂ J₂)
    (fun u=>by positivity) (fun v=>by positivity) E hE ?_
  · simpa only [f,g,←plain_column_integral S a ha c τ₁ t₁ θ₁ X hX V₁ hc₁ hs₁,
      ←plain_column_integral T b hb d τ₂ t₂ θ₂ Y hY V₂ hc₂ hs₂] using hh
  · intro u v
    simp only [f,g,norm_mul,logPhase_norm,mul_one]
    calc
      _=(‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ v‖)*
        (∑z∈rows,
          ‖rowPolynomial S a (fun i=>c i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) z‖*
          ‖rowPolynomial T b (fun j=>d j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) z‖):=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _≤(‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ v‖)*
          (E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):=
        mul_le_mul_of_nonneg_left (hpair u v) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _=_:=by ring

end SevenEighths.CenteredMomentExceptionalWindowPair

end

end OAI

end Source1900

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalIndexedWindow.lean; sha256: a697da96db63aeb56139b213f2b9972e7da600667466aef3a354a4185fc08bbe -/
section Source1901
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalIndexedWindow
open CenteredMomentExceptionalWindowPair CenteredMomentPlainWindowEnergy
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem indexed_plain_window_pair {κ α β:Type*}
    (rows:Finset κ)(row:κ→O)(S:Finset α)(T:Finset β)(a:α→O)(b:β→O)
    (ha:∀i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (hb:∀j,CanonicalQuadraticSieve.Supported (Ideal.span {b j}))
    (c:κ→α→ℂ)(d:κ→β→ℂ)(τ₁ τ₂:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u v:ℝ,(∑z∈rows,
      ‖rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) (row z)‖*
      ‖rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) (row z)‖)≤
        E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):
    (∑z∈rows,
      ‖rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ t₁ (Ideal.span {a i})*
        columnPhase V₁ (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ₁) (row z)‖*
      ‖rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ t₂ (Ideal.span {b j})*
        columnPhase V₂ (Real.log ((Ideal.absNorm (Ideal.span {b j}):ℝ)/Y)) θ₂) (row z)‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫v:ℝ,(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖):=by
  let f:=fun z:κ=>fun u:ℝ=>columnDensity V₁ hc₁ hs₁ u*logPhase (θ₁-u) (Real.log X)*
    rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) (row z)
  let g:=fun z:κ=>fun v:ℝ=>columnDensity V₂ hc₂ hs₂ v*logPhase (θ₂-v) (Real.log Y)*
    rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) (row z)
  have hf (z:κ):Integrable (f z):=plain_column_integrable S a ha (c z) τ₁ t₁ θ₁ X hX V₁ hc₁ hs₁ (row z)
  have hg (z:κ):Integrable (g z):=plain_column_integrable T b hb (d z) τ₂ t₂ θ₂ Y hY V₂ hc₂ hs₂ (row z)
  have hh:=paired_integrals rows f g (fun z _=>hf z) (fun z _=>hg z)
    (fun u=>(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)
    (fun v=>(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖)
    (columnDensity_moments V₁ hc₁ hs₁ J₁) (columnDensity_moments V₂ hc₂ hs₂ J₂)
    (fun u=>by positivity) (fun v=>by positivity) E hE ?_
  · have hfEq (z:κ):
        (∫u:ℝ,f z u)=rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ t₁ (Ideal.span {a i})*
          columnPhase V₁ (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ₁) (row z):=
        (plain_column_integral S a ha (c z) τ₁ t₁ θ₁ X hX V₁ hc₁ hs₁ (row z)).symm
    have hgEq (z:κ):
        (∫v:ℝ,g z v)=rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ t₂ (Ideal.span {b j})*
          columnPhase V₂ (Real.log ((Ideal.absNorm (Ideal.span {b j}):ℝ)/Y)) θ₂) (row z):=
        (plain_column_integral T b hb (d z) τ₂ t₂ θ₂ Y hY V₂ hc₂ hs₂ (row z)).symm
    simpa only [hfEq,hgEq] using hh
  · intro u v
    simp only [f,g,norm_mul,logPhase_norm,mul_one]
    calc
      _=(‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ v‖)*
        (∑z∈rows,
          ‖rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) (row z)‖*
          ‖rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) (row z)‖):=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _≤(‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ v‖)*
          (E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):=
        mul_le_mul_of_nonneg_left (hpair u v) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _=_:=by ring

end SevenEighths.CenteredMomentExceptionalIndexedWindow

end

end OAI

end Source1901

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalWholeWindow.lean; sha256: 7d7b5163b140412c0b94eac22c3a0f646c439f9af5a3fe70f113eed592985d9c -/
section Source1902
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalWholeWindow
open CenteredMomentExceptionalIndexedWindow CenteredMomentPlainWindowEnergy
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem rowPolynomial_factor {α:Type*}(S:Finset α)(a:α→O)(c:α→ℂ)(v:ℂ)(z:O):
    rowPolynomial S a (fun i=>v*c i) z=v*rowPolynomial S a c z:=by
  simp only [rowPolynomial,Finset.mul_sum,mul_assoc]

theorem whole_plain_window_pair {γ α β:Type*}
    (Ds:Finset γ)(μ:γ→ℂ)(rows:Finset O)(S:Finset α)(T:Finset β)(a:α→O)(b:β→O)
    (ha:∀i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (hb:∀j,CanonicalQuadraticSieve.Supported (Ideal.span {b j}))
    (c:γ→α→ℂ)(d:γ→β→ℂ)(τ₁ τ₂:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u v:ℝ,(∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖rowPolynomial S a (fun i=>c L i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) z‖*
      ‖rowPolynomial T b (fun j=>d L j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) z‖)≤
        E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):
    (∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖rowPolynomial S a (fun i=>c L i*heightCoeff τ₁ t₁ (Ideal.span {a i})*
        columnPhase V₁ (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ₁) z‖*
      ‖rowPolynomial T b (fun j=>d L j*heightCoeff τ₂ t₂ (Ideal.span {b j})*
        columnPhase V₂ (Real.log ((Ideal.absNorm (Ideal.span {b j}):ℝ)/Y)) θ₂) z‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫v:ℝ,(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖):=by
  have hh:=indexed_plain_window_pair (Ds×ˢrows) (fun x:γ×O=>x.2) S T a b ha hb
    (fun x i=>μ x.1*c x.1 i) (fun x j=>d x.1 j) τ₁ τ₂ t₁ t₂ θ₁ θ₂ X Y hX hY
    V₁ V₂ hc₁ hc₂ hs₁ hs₂ J₁ J₂ E hE ?_
  · simpa only [mul_assoc,rowPolynomial_factor,norm_mul,
      Finset.sum_product,Finset.mul_sum,mul_assoc] using hh
  · intro u v
    simpa only [mul_assoc,rowPolynomial_factor,norm_mul,
      Finset.sum_product,Finset.mul_sum,mul_assoc] using hpair u v

end SevenEighths.CenteredMomentExceptionalWholeWindow

end

end OAI

end Source1902

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonWindowColumn.lean; sha256: 30a8f655a64f330e71c5838c8c7d077cfe9f499fbaf4263987b348a8d73d65df -/
section Source1903
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentCommonWindowColumn
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonPairedSource
open CenteredMomentCommonLinearSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentExceptionalWholeWindow CenteredMomentSmooth
local notation "O" => HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def columns (s:Input ι)(C:Ideal O)(hC:Supported C):Finset (Ideal O):=
  residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))

def coefficient (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (I:supportedColumns (columns s C hC)):ℂ:=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*
    (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then
      finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I) else 0)

def windowColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
    (fun I=>coefficient s C hC R seed L I*heightCoeff η t I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z

omit [DecidableEq ι] in
theorem coefficient_polynomial (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t:ℝ)(z:O):
    rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
      (fun I=>coefficient s C hC R seed L I*heightCoeff η t I) z=
      normalizedColumn (withHeight s η t) C hC R seed L z:=by
  unfold normalizedColumn sourceColumn
  dsimp only [withHeight,Input.pools,columns]
  simp only [coefficient,mul_assoc,rowPolynomial_factor,Input.pools,columns]
  rfl

theorem sourceGenerator_span (S:Finset (Ideal O))(I:supportedColumns S):
    Ideal.span {sourceGenerator S I}=(I:Ideal O):=
  primary_span_supported I (Finset.mem_filter.mp I.property).2

omit [DecidableEq ι] in
theorem whole_window_pair (s v:Input ι)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed:Ideal O)(Ds:Finset (Ideal O))(μ:Ideal O→ℂ)(rows:Finset O)
    (η τ:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u w:ℝ,(∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖normalizedColumn (withHeight s η (t₁+2*Real.pi*(u-θ₁))) C hC R seed L z‖*
      ‖normalizedColumn (withHeight v τ (t₂+2*Real.pi*(w-θ₂))) D hD R seed L z‖)≤
        E*(1+‖u‖)^J₁*(1+‖w‖)^J₂):
    (∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖windowColumn s C hC R seed L η t₁ θ₁ X V₁ z‖*
      ‖windowColumn v D hD R seed L τ t₂ θ₂ Y V₂ z‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫w:ℝ,(1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖):=by
  have hh:=whole_plain_window_pair Ds μ rows Finset.univ Finset.univ
    (sourceGenerator (columns s C hC)) (sourceGenerator (columns v D hD))
    (sourceGenerator_supported _) (sourceGenerator_supported _)
    (coefficient s C hC R seed) (coefficient v D hD R seed) η τ t₁ t₂ θ₁ θ₂ X Y hX hY
    V₁ V₂ hc₁ hc₂ hs₁ hs₂ J₁ J₂ E hE ?_
  · simpa only [sourceGenerator_span,windowColumn] using hh
  · intro u w
    simpa only [sourceGenerator_span,coefficient_polynomial] using hpair u w

end SevenEighths.CenteredMomentCommonWindowColumn

end

end OAI

end Source1903

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonSectorWindow.lean; sha256: db5f358caeb851c8cf8c5179359a0f1e6cf1828be4c6add1c1e222ad3ac59eb6 -/
section Source1904
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonSectorWindow
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentSecondMaskedWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalWholeWindow CenteredMomentSmooth CenteredMomentSecondWindowSource
open RayFourExpansion CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem actual_sector_window (s:Input ι)(η τ:Character)(χ:RayCharacter)(A:O)
    (C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(t θ X:ℝ)(V:ℝ→ℂ)(z:O)
    (hτ:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z=
      windowColumn s C hC R seed L τ t θ X V z:=by
  dsimp only
  simp_rw [masked_divisor_coefficient η τ χ A C hC hτ]
  rw [sector_rowPolynomial _ (fun I=>(if L∣I then finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I) else 0)*
      heightCoeff τ t I*columnPhase V (Real.log ((Ideal.absNorm I:ℝ)/X)) θ) C hC z]
  unfold windowColumn
  rw [←rowPolynomial_factor]
  apply congrArg (fun c=>rowPolynomial Finset.univ (sourceGenerator (columns s C hC)) c z)
  funext I
  dsimp only [coefficient]
  split_ifs <;> simp_all ; ring

omit [DecidableEq ι] in
theorem window_neg (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t θ X:ℝ)(V:ℝ→ℂ)(z:O):
    windowColumn s C hC R seed L η t θ X V (-z)=
      windowColumn s C hC R seed L (reflected η) t θ X V z:=by
  unfold windowColumn rowPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only
  rw [reflected_height η t I (Finset.mem_filter.mp I.property).2,
    show -z=(-1)*z by ring,idealRowHom_argument_mul,sourceGenerator_span]
  ring

omit [DecidableEq ι] in
theorem actual_reflected_sector_window (s:Input ι)(η τ:Character)(χ:RayCharacter)(A:O)
    (C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(t θ X:ℝ)(z:O)
    (hτ:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
        star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ)) (-z)=
      windowColumn s C hC R seed L (reflected τ) t (-θ) X logAnnulus z:=by
  dsimp only
  simp only [star_logAnnulus_column]
  rw [actual_sector_window s η τ χ A C hC R seed L t (-θ) X logAnnulus (-z) hτ,window_neg]

end SevenEighths.CenteredMomentCommonSectorWindow

end

end OAI

end Source1904

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalPairDictionary.lean; sha256: 821259e00d2fe36384f3152ddf507da641b660f80c0b3c0d5158442385e51bc2 -/
section Source1905
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondExceptionalPairDictionary
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

lemma raw_pair (V:ℝ)(hV:0<V)(a b:ℂ):
    ‖a‖*‖b‖=V*‖(Real.sqrt V:ℂ)⁻¹*a‖*‖(Real.sqrt V:ℂ)⁻¹*b‖:=by
  have hs:0<Real.sqrt V:=Real.sqrt_pos.mpr hV
  simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  field_simp
  rw [Real.sq_sqrt hV.le]

omit [DecidableEq ι] in
theorem original_pair (s:Input ι)(η τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y:ℝ)(Ds:Finset (Ideal O))(rows:Finset O)
    (hτ₁:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ₁ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (hτ₂:∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
      heightCoeff τ₂ v I=heightCoeff η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
        (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
          (movingCoefficient A (sectorElement C hC.1 S)
            (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
          columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) w) z‖*
      ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*
          star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) w)) (-z)‖)=
      volume s.toData*(∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖windowColumn s C hC R seed L τ₁ t w X logAnnulus z‖*
        ‖windowColumn s D hD R seed L (reflected τ₂) t (-w) Y logAnnulus z‖):=by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L hL
  rw [mul_left_comm (volume s.toData) ‖(moebius L:ℂ)‖]
  apply congrArg (fun a:ℝ=>‖(moebius L:ℂ)‖*a)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [raw_pair (volume s.toData) (volume_pos s.toData)]
  rw [actual_sector_window s η τ₁ χ A C hC R seed L t w X logAnnulus z hτ₁,
    actual_reflected_sector_window s η τ₂ ξ A D hD R seed L t w Y z hτ₂]
  ring

end SevenEighths.CenteredMomentSecondExceptionalPairDictionary

end

end OAI

end Source1905

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalHeight.lean; sha256: 3a3f7a0f203ed69a525e5bb4ab9f9840164a3a10a8c0cdefb392da843091eb0a -/
section Source1906
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalHeight
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentHeckeWindowEnergy HeckeFamily CenteredMomentAllocatedDetectorAmplitude
universe u

def cost (p:Tests)(t θ:ℝ):ℝ:=‖p.height 0‖+‖p.height 1‖+heightCost t θ

theorem cost_pos (p:Tests)(t θ:ℝ):0<cost p t θ:=by
  dsimp only [cost]
  linarith [norm_nonneg (p.height 0),norm_nonneg (p.height 1),heightCost_pos t θ]

theorem shifted_weight (p:Tests)(t θ u:ℝ):
    p.heightWeight (t+2*Real.pi*(u-θ))≤cost p t θ*(1+‖u‖):=by
  have h:=norm_height_shift t θ u
  dsimp only [Tests.heightWeight,cost]
  nlinarith [mul_nonneg (norm_nonneg (p.height 0)) (norm_nonneg u),
    mul_nonneg (norm_nonneg (p.height 1)) (norm_nonneg u)]

def mass {ι κ:Type u}[Fintype ι][Fintype κ]
    (s:Input ι)(v:Input κ)(p q:Tests)(t₁ t₂ θ₁ θ₂:ℝ)(J:ℕ):ℝ:=
  cost p t₁ θ₁^J*cost q t₂ θ₂^J*slotControl s.toData*slotControl v.toData*
    Real.sqrt (volume s.toData)*Real.sqrt (volume v.toData)

theorem mass_nonneg {ι κ:Type u}[Fintype ι][Fintype κ]
    (s:Input ι)(v:Input κ)(p q:Tests)(t₁ t₂ θ₁ θ₂:ℝ)(J:ℕ):
    0≤mass s v p q t₁ t₂ θ₁ θ₂ J:=by
  unfold mass
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (pow_nonneg (cost_pos p t₁ θ₁).le _) (pow_nonneg (cost_pos q t₂ θ₂).le _))
    (slotControl_nonneg _)) (slotControl_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem shifted_mass {ι κ:Type u}[Fintype ι][Fintype κ][DecidableEq ι][DecidableEq κ]
    (s:Input ι)(v:Input κ)(η τ:Character)(p q:Tests)(t₁ t₂ θ₁ θ₂ u w:ℝ)(J:ℕ):
    profileMass (withHeight s η (t₁+2*Real.pi*(u-θ₁))).toData
      (withHeight v τ (t₂+2*Real.pi*(w-θ₂))).toData p q J≤
      mass s v p q t₁ t₂ θ₁ θ₂ J*(1+‖u‖)^J*(1+‖w‖)^J:=by
  have hp:=pow_le_pow_left₀ (by dsimp [Tests.heightWeight];positivity)
    (shifted_weight p t₁ θ₁ u) J
  have hq:=pow_le_pow_left₀ (by dsimp [Tests.heightWeight];positivity)
    (shifted_weight q t₂ θ₂ w) J
  have hh:=mul_le_mul hp hq (by dsimp [Tests.heightWeight];positivity)
    (pow_nonneg (mul_nonneg (cost_pos p t₁ θ₁).le (by positivity)) _)
  have hs:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (slotControl_nonneg s.toData))
      (slotControl_nonneg v.toData)) (Real.sqrt_nonneg (volume s.toData)))
      (Real.sqrt_nonneg (volume v.toData))
  convert hs using 1
  · rfl
  · simp only [mass,mul_pow];ring

end SevenEighths.CenteredMomentExceptionalHeight

end

end OAI

end Source1906

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonExceptionalWindow.lean; sha256: 62a8a8d029518f410d8502d86bd4053408e8206fc4bc193c9130fd38120f596a -/
section Source1907
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentCommonExceptionalWindow
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonExceptionalSource CenteredMomentCommonExceptionalCost
open CenteredMomentCommonPairedSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonWindowColumn
open CenteredMomentExceptionalHeight CenteredMomentHeckeColumnWindow CenteredMomentSmooth
open CenteredMomentSecondHeightFamily CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_common_window (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Tests),(∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤s.X₁ → Z^rLeft≤s.X₂ → Z^rLeft≤s.Y₁ → Z^rLeft≤s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀θ₁ θ₂ X Y:ℝ,0<X → 0<Y →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖windowColumn s C hC R seed L s.η s.t θ₁ X logAnnulus z‖*
        ‖windowColumn v D hD R seed L v.η v.t θ₂ Y logAnnulus z‖)≤
        K*(rows.card:ℝ)*Z^(2*ε+δ-max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm))*
          mass s v p q s.t v.t θ₁ θ₂ J*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2 :=by
  obtain ⟨J,hJ⟩:=actual_common_exceptional lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond
    θ₁ θ₂ X Y hX hY Ds hDs
  let F:=K*(rows.card:ℝ)*Z^(2*ε+δ-max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm))
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (by positivity) (div_nonneg
      (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg v)) (by positivity))
  have hh:=whole_window_pair s v C D hC hD R seed Ds (fun L=>(moebius L:ℂ)) rows
    s.η v.η s.t v.t θ₁ θ₂ X Y hX hY logAnnulus logAnnulus
    logAnnulus_compact logAnnulus_compact logAnnulus_smooth logAnnulus_smooth
    J J (F*mass s v p q s.t v.t θ₁ θ₂ J)
    (mul_nonneg hF (mass_nonneg s v p q s.t v.t θ₁ θ₂ J)) ?_
  · simpa only [F,pow_two,mul_assoc] using hh
  intro u w
  have hb:=hZ.2 (withHeight s s.η (s.t+2*Real.pi*(u-θ₁)))
    (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))) p q hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂
    C D hC hD R seed hR hsC hsD rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂
    rows hn hsEx hvEx hsCond hvCond Ds hDs
  have hm:=shifted_mass s v s.η v.η p q s.t v.t θ₁ θ₂ u w J
  apply hb.trans
  calc
    _=F*profileMass (withHeight s s.η (s.t+2*Real.pi*(u-θ₁))).toData
        (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))).toData p q J:=by
      dsimp only [F,frozenProfile,withHeight]
      ring
    _≤F*(mass s v p q s.t v.t θ₁ θ₂ J*(1+‖u‖)^J*(1+‖w‖)^J):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by ring

end SevenEighths.CenteredMomentCommonExceptionalWindow

end

end OAI

end Source1907

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalWindowHeight.lean; sha256: 3117dbe667d55a662f53d0f85d63bc7f4bc4896a1692157fa0a40aa3a68dc9a3 -/
section Source1908
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalWindowHeight
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentCommonRadialData CenteredMomentExceptionalHeight
open CenteredMomentHeckeWindowEnergy CenteredMomentAllocatedDetectorAmplitude
universe u

theorem cost_phase (p:Tests)(t θ:ℝ):
    cost p t θ≤p.heightWeight t*(1+2*Real.pi)^2*(1+‖θ‖):=by
  have hc:0≤2*Real.pi:=by positivity
  have hp:1≤p.heightWeight t:=by
    dsimp only [Tests.heightWeight]
    linarith [norm_nonneg (p.height 0),norm_nonneg (p.height 1),norm_nonneg t]
  have h1:cost p t θ≤(p.heightWeight t+2*Real.pi*‖θ‖)*(1+2*Real.pi):=by
    dsimp only [cost,Tests.heightWeight,heightCost]
    nlinarith [mul_nonneg hc (norm_nonneg (p.height 0)),mul_nonneg hc (norm_nonneg (p.height 1))]
  have h2:p.heightWeight t+2*Real.pi*‖θ‖≤p.heightWeight t*(1+2*Real.pi)*(1+‖θ‖):=by
    nlinarith [mul_nonneg hc (norm_nonneg θ),mul_nonneg hc (show 0≤p.heightWeight t by linarith),
      mul_nonneg (show 0≤p.heightWeight t-1 by linarith) (mul_nonneg hc (norm_nonneg θ)),
      mul_nonneg (show 0≤p.heightWeight t by linarith) (norm_nonneg θ)]
  exact h1.trans ((mul_le_mul_of_nonneg_right h2 (by positivity)).trans_eq (by ring))

theorem mass_phase {ι κ:Type u}[Fintype ι][Fintype κ][DecidableEq ι][DecidableEq κ]
    (s:Input ι)(v:Input κ)(p q:Tests)(w:ℝ)(J:ℕ):
    mass s v p q s.t v.t w (-w) J≤
      (1+2*Real.pi)^(4*J)*profileMass s.toData v.toData p q J*(1+‖w‖)^(2*J):=by
  have hp:=pow_le_pow_left₀ (cost_pos p s.t w).le (cost_phase p s.t w) J
  have hq:=pow_le_pow_left₀ (cost_pos q v.t (-w)).le (cost_phase q v.t (-w)) J
  rw [norm_neg] at hq
  have hh:=mul_le_mul hp hq (pow_nonneg (cost_pos q v.t (-w)).le _) (by dsimp only [Tests.heightWeight]; positivity)
  have he:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (slotControl_nonneg s.toData))
      (slotControl_nonneg v.toData)) (Real.sqrt_nonneg (volume s.toData)))
        (Real.sqrt_nonneg (volume v.toData))
  apply he.trans_eq
  simp only [profileMass,mul_pow,←pow_mul]
  rw [show 4*J=2*J+2*J by omega,show 2*J=J+J by omega]
  simp only [pow_add]
  ring

end SevenEighths.CenteredMomentExceptionalWindowHeight

end

end OAI

end Source1908

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalPairBound.lean; sha256: 346bea31018789d3e9f22a1215e99ba273d329192eb00a3460a4dd3f1f0b4cdc -/
section Source1909
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalPairBound
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonExceptionalWindow CenteredMomentExceptionalWindowHeight
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def originalPair (s:Input ι)(η:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y:ℝ)(Ds:Finset (Ideal O))(rows:Finset O):ℝ:=
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
        (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
          (movingCoefficient A (sectorElement C hC.1 S)
            (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
          columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) w) z‖*
      ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*
          star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) w)) (-z)‖)

omit [DecidableEq ι] in
lemma window_withHeight (s:Input ι)(τ η:Character)(v t θ X:ℝ)(C:Ideal O)(hC:Supported C)
    (R seed L:Ideal O)(V:ℝ→ℂ)(z:O):
    windowColumn (withHeight s τ v) C hC R seed L η t θ X V z=
      windowColumn s C hC R seed L η t θ X V z:=rfl

theorem actual_original_pair (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀(τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O),
      (∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
        heightCoeff τ₁ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
        heightCoeff τ₂ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)) →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₁ Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₂ Q fixedBadMask 1 (-z)) →
      (∀z∈rows,(τ₁.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,((reflected τ₂).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(X Y:ℝ),0<X → 0<Y → ∀Ds:Finset (Ideal O),
      (∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) → ∀w:ℝ,
      originalPair s s.η χ ξ A C D hC hD R seed s.t w X Y Ds rows≤
        (K*(rows.card:ℝ)*Z^(2*ε+δ-max (r-Real.logb Z (C.absNorm:ℝ)) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          ((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*
            frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2)*
          (1+‖w‖)^(2*J):=by
  obtain ⟨J,hJ⟩:=actual_common_window lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R seed hR hsC hsD r hX₁ hX₂ hY₁ hY₂
    τ₁ τ₂ χ ξ A hτ₁ hτ₂ rows hn hex₁ hex₂ hcond₁ hcond₂ X Y hX hY Ds hDs w
  have hex₂':∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (reflected τ₂) Q fixedBadMask 1 z:=by
    intro z hz
    exact (reflected_inducing τ₂ Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hex₂ z hz)
  have hb:=hZ.2 (withHeight s τ₁ s.t) (withHeight s (reflected τ₂) s.t) p p hlo hhi
    hP hP hW₁ hW₂ hW₁ hW₂ C D hC hD R seed hR hsC hsD r r
    hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂ rows hn hex₁ hex₂' hcond₁ hcond₂ w (-w) X Y hX hY Ds hDs
  simp only [window_withHeight] at hb
  rw [originalPair,original_pair s s.η τ₁ τ₂ χ ξ A C D hC hD R seed s.t w X Y Ds rows hτ₁ hτ₂]
  apply (mul_le_mul_of_nonneg_left hb (volume_pos s.toData).le).trans
  have hm:=mass_phase s s p p w J
  let F:=volume s.toData*(K*(rows.card:ℝ)*Z^(2*ε+δ-max (r-Real.logb Z (C.absNorm:ℝ)) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm)))*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (volume_pos s.toData).le
      (mul_nonneg (by positivity) (div_nonneg (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg s))
        (by positivity)))) (sq_nonneg _)
  calc
    _=F*mass s s p p s.t s.t w (-w) J:=by
      dsimp only [F,frozenProfile,withHeight,mass,
        CenteredMomentAllocatedDetectorAmplitude.slotControl,CenteredMomentExceptionalAmplitudePair.volume]
      ring
    _≤F*((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*(1+‖w‖)^(2*J)):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentSecondExceptionalPairBound

end

end OAI

end Source1909

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondDivisorSupport.lean; sha256: d08f1a4168785e953e853795ba6ecb047687711af09bd352311dee1a22cde0c0 -/
section Source1910
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSecondDivisorSupport
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondExceptionalPairBound RayFourExpansion
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem live_right_divisor_norm (D I L:Ideal O)(hD:D≠0)(hI:I≠0)
    (β:Ideal O→ℂ)(H:ℝ)(hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)
    (hne:β (D*I)≠0)(hLI:L∣I):
    (L.absNorm:ℝ)≤H/(D.absNorm:ℝ):=by
  have hDpos:(0:ℝ)<D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hnorm:(L.absNorm:ℝ)≤I.absNorm:=by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)) (map_dvd Ideal.absNorm hLI)
  have hb:=hβ (D*I) hne
  rw [map_mul,Nat.cast_mul] at hb
  apply hnorm.trans
  apply (le_div_iff₀ hDpos).mpr
  simpa only [mul_comm] using hb

theorem right_divisor_coefficient_zero
    (D:Ideal O)(hD:Supported D)(S:Finset (Ideal O))(β:Ideal O→ℂ)(H:ℝ)
    (hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)(L:Ideal O)(hL:H/(D.absNorm:ℝ)<L.absNorm)
    (η:Character)(t:ℝ)(A:O)(ξ:RayCharacter)(I:sectorPool D hD.1 S):
    divisorCoefficient L (sectorElement D hD.1 S)
      (movingCoefficient A (sectorElement D hD.1 S)
        (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I=0:=by
  unfold divisorCoefficient
  rw [sectorElement_span]
  split_ifs with hd
  · have hz:β (D*I)=0:=by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (sectorPool_supported D hD.1 S I).1 β H hβ hn hd)
    simp only [movingCoefficient,hz,zero_mul]
  · rfl

theorem right_divisor_row_zero
    (D:Ideal O)(hD:Supported D)(S:Finset (Ideal O))(β:Ideal O→ℂ)(H:ℝ)
    (hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)(L:Ideal O)(hL:H/(D.absNorm:ℝ)<L.absNorm)
    (η:Character)(t:ℝ)(A:O)(ξ:RayCharacter)(v:sectorPool D hD.1 S→ℂ)(z:O):
    rowPolynomial Finset.univ (sectorElement D hD.1 S)
      (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
        (movingCoefficient A (sectorElement D hD.1 S)
          (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*v I) z=0:=by
  unfold rowPolynomial
  apply Finset.sum_eq_zero
  intro I hI
  exact mul_eq_zero_of_left
    (mul_eq_zero_of_left (right_divisor_coefficient_zero D hD S β H hβ L hL η t A ξ I) _) _

theorem originalPair_filter_right {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(η:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y H:ℝ)(Ds:Finset (Ideal O))(rows:Finset O)
    (hβ:∀I:Ideal O,finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I≠0→
      (I.absNorm:ℝ)≤H):
    originalPair s η χ ξ A C D hC hD R seed t w X Y Ds rows=
      originalPair s η χ ξ A C D hC hD R seed t w X Y
        (Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ))) rows:=by
  unfold originalPair
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hLD
  by_cases hL:(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)
  · rw [ite_eq_left hL]
  · rw [ite_eq_right hL]
    have hz:=right_divisor_row_zero D hD (finiteColumns (Fintype.piFinset s.pools))
      (finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed))
      H hβ L (lt_of_not_ge hL) η t A ξ
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro z hzr
    apply mul_eq_zero_of_right
    exact norm_eq_zero.mpr (hz _ _)

end SevenEighths.CenteredMomentSecondDivisorSupport

end

end OAI

end Source1910

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSupportedChildren.lean; sha256: 965b193db93606eea206de355658f652730efa88e846321608a4bb514a34be2e -/
section Source1911
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondSupportedChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound CenteredMomentSecondDivisorSupport CenteredMomentSourceRow
open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSecondOriginalChildren
local notation "O" => ActualEisensteinCubic.O

theorem paired_rows_filter_right
    (D:Ideal O) (hD:Supported D) (S:Finset (Ideal O)) (β:Ideal O→ℂ) (Hsource:ℝ)
    (hβ:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (η:Character) (t:ℝ) (A:O) (ξ:RayCharacter)
    (v:Ideal O→sectorPool D hD.1 S→ℂ) (argument:O→O)
    (Ds:Finset (Ideal O)) (rows:Finset O) (scalar:Ideal O→ℂ) (left:Ideal O→O→ℂ) :
    (∑L∈Ds,scalar L*∑z∈rows,left L z*star
      (rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*v L I)
        (argument z)))=
    ∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)),
      scalar L*∑z∈rows,left L z*star
      (rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*v L I)
        (argument z)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hL
  by_cases hn:(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)
  · rw [ite_eq_left hn]
  · rw [ite_eq_right hn]
    have hz:=right_divisor_row_zero D hD S β Hsource hβ L (lt_of_not_ge hn) η t A ξ
    simp only [hz,star_zero,mul_zero,Finset.sum_const_zero]

theorem right_source_energy_zero
    (D:Ideal O) (hD:Supported D) (S:Finset (Ideal O)) (β:Ideal O→ℂ) (Hsource:ℝ)
    (hβ:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (L:Ideal O) (hL:Hsource/(D.absNorm:ℝ)<L.absNorm)
    (keep:O→Prop) (f:Ideal O→ℂ) (Φ:𝓢(ℝ,ℂ)) (H:ℝ) :
    sourceRestrictedEnergy keep (residualPool D hD.1 S)
      (fun I=>if IsCoprime D I ∧ L∣I then β (D*I) else 0) f Φ H=0 := by
  have hc (I:supportedColumns (residualPool D hD.1 S)) :
      (if IsCoprime D (I:Ideal O) ∧ L∣(I:Ideal O) then β (D*I) else 0)=0 := by
    split_ifs with hi
    · by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (Finset.mem_filter.mp I.property).2.1 β Hsource hβ hn hi.2)
    · rfl
  simp only [sourceRestrictedEnergy,restrictedEnergy,rowPolynomial,hc,zero_mul,
    Finset.sum_const_zero,norm_zero,zero_pow (by decide:2≠0),ite_self,tsum_zero]

theorem actual_block_from_supported_envelopes (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀r:ℝ,0<r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
        (C D:Ideal O) (hC:Supported C) (hD:Supported D),
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀Hsource:ℝ,(∀I,β I≠0→(I.absNorm:ℝ)≤Hsource) →
      Hsource/(D.absNorm:ℝ)≤Z^B →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0<X → 0<Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),0<H →
      (∀z:O,0≤(Φ (normValue z/H)).re) → (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool C hC.1 S)
          (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤(E₁/(Ideal.absNorm L:ℝ))*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool D hD.1 S)
          (fun I=>if IsCoprime D I ∧ L∣I then β (D*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤(E₂/(Ideal.absNorm L:ℝ))*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        C0*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨K,hK,hkernel⟩:=CenteredMomentSecondSquarefreeBlock.actual_block_from_squarefree_source W decay J₁ J₂
  obtain ⟨Cm,hCm,hmass⟩:=CenteredMomentMobiusHarmonicMass.full_mass_subpower B δ hB hδ
  refine ⟨max 1 K*Cm,mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hCm,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t S β C D hC hD hCD U A hτ Hsource hβ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  let live (L:Ideal O):Prop:=(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)
  let Ds:=divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O))
  let coarse (L:Ideal O):ℝ:=QuadraticInitialBound.diagonalControl Φ*max 1 H*
    (∑I∈residualPool C hC.1 S,‖if IsCoprime C I ∧ L∣I then β (C*I) else 0‖)^2
  have hcoarse (L:Ideal O):0≤coarse L:=
    mul_nonneg (mul_nonneg (QuadraticInitialBound.diagonalControl_nonneg Φ) (by positivity)) (sq_nonneg _)
  let F₁:Ideal O→ℝ:=fun L=>if live L then E₁/(L.absNorm:ℝ) else coarse L
  let F₂:Ideal O→ℝ:=fun L=>if live L then E₂/(L.absNorm:ℝ) else 0
  have hF₁ (L:Ideal O):0≤F₁ L:=by
    dsimp only [F₁];split_ifs
    · exact div_nonneg hE₁ (Nat.cast_nonneg _)
    · exact hcoarse L
  have hF₂ (L:Ideal O):0≤F₂ L:=by
    dsimp only [F₂];split_ifs
    · exact div_nonneg hE₂ (Nat.cast_nonneg _)
    · exact le_rfl
  have hk:=hkernel r hr η τ t S β C D hC hD hCD U hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor F₁ F₂ hF₁ hF₂
    (by
      intro L hL hsf χ v
      by_cases hl:live L
      · simpa only [F₁,ite_eq_left hl] using hleft L hL hl hsf χ v
      · have hh:=CenteredMomentSourceAbsoluteEnvelope.actual_source_absolute (residualPool C hC.1 S)
          (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (τ χ) v
          (nonexceptional η χ Q m A) Φ H hH
        exact hh.trans (by simpa only [F₁,ite_eq_right hl] using
          le_mul_of_one_le_right (hcoarse L) (one_le_pow₀ (by linarith [norm_nonneg v]) (n:=2*J₁))))
    (by
      intro L hL hsf χ v
      by_cases hl:live L
      · simpa only [F₂,ite_eq_left hl] using hright L hL hl hsf χ v
      · rw [right_source_energy_zero D hD S β Hsource hβ L (lt_of_not_ge hl)]
        simp only [F₂,ite_eq_right hl,zero_mul,le_refl])
  have he:(∑L∈Ds,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
      (windowBudget J₁ t (F₁ L)*windowBudget J₂ t (F₂ L)))=
      (∑L∈Ds.filter live,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂):=by
    rw [Finset.sum_mul,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L hL
    by_cases hl:live L
    · rw [ite_eq_left hl]
      simp only [F₁,F₂,ite_eq_left hl]
      rw [CenteredMomentSecondHarmonicBudget.paired_divisor J₁ J₂ t E₁ E₂ _ (Nat.cast_nonneg _)]
      ring
    · have hl' : ¬(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ):=hl
      simp only [F₂,live,ite_eq_right hl',windowBudget,Real.sqrt_zero,zero_mul,mul_zero]
  have hmass':(∑L∈Ds.filter live,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))≤Cm*Z^δ:=
    hZ.2 (Ds.filter live) (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hn)
  apply hk.trans
  change K*(∑L∈Ds,_)≤_
  rw [he]
  calc
    _≤K*(Cm*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂)):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmass'
        (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _))) hK
    _≤max 1 K*(Cm*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂)):=
      mul_le_mul_of_nonneg_right (le_max_right _ _)
        (mul_nonneg (mul_nonneg hCm.le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
          (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))
    _=_:=by ring

variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem actual_block_from_supported_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0 Ce:ℝ,0<C0 ∧ 0<Ce ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀r:ℝ,0<r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (s:Input ι),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀Hsource:ℝ,(∀I,β I≠0→(I.absNorm:ℝ)≤Hsource) →
      Hsource/(D.absNorm:ℝ)≤Z^B →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0<X → 0<Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),∀hH:0<H,
      ∀hΦ:(∀z:O,0≤(Φ (normValue z/H)).re), (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤E₂*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        C0*Z^δ*(windowBudget J₁ t (core s C Ce Z δ E₁)*windowBudget J₂ t (core s D Ce Z δ E₂)) := by
  obtain ⟨Ce,hCe,hsource⟩:=actual_height_envelope lo hi B δ hB hδ
  obtain ⟨C0,hC0,hkernel⟩:=actual_block_from_supported_envelopes W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,Ce,hC0,hCe,?_⟩
  filter_upwards [hkernel] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t s hlo hhi R0 seed S β C D hC hD hsC hsD hnC hnD hCD U A hτ Hsource hβ hn
    R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hcore (G:Ideal O) (E:ℝ) (hE:0≤E):0≤core s G Ce Z δ E:=by
    unfold core
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCe.le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
      (mul_nonneg (profileCost_nonneg s) hE))
      (mul_nonneg (mul_nonneg s.X₁_pos.le s.X₂_pos.le) (Finset.prod_nonneg (fun i _=>(s.P_pos i).le)))) (Nat.cast_nonneg _)
  apply hZ.2 r hr η τ t S β C D hC hD hCD U hτ Hsource hβ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor (core s C Ce Z δ E₁) (core s D Ce Z δ E₂)
    (hcore C E₁ hE₁) (hcore D E₂ hE₂)
  · intro L hL hcap hsf χ v
    have hNL: (Ideal.absNorm L:ℝ)≤Z^B:=hcap.trans hn
    have hh:=hsource s hlo hhi (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) C hC R0 seed L hsC hsf
      E₁ Z hE₁ hZ.1 hnC hNL J₁ (τ χ) v (hleft L hL hcap hsf χ v)
    simpa only [envelope_eq_core,sourceRadial,S,β,A] using hh
  · intro L hL hcap hsf χ v
    have hNL: (Ideal.absNorm L:ℝ)≤Z^B:=hcap.trans hn
    have hh:=hsource s hlo hhi (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) D hD R0 seed L hsD hsf
      E₂ Z hE₂ hZ.1 hnD hNL J₂ (τ χ) v (hright L hL hcap hsf χ v)
    simpa only [envelope_eq_core,sourceRadial,S,β,A] using hh

end SevenEighths.CenteredMomentSecondSupportedChildren

end

end OAI

end Source1911

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondNonexceptionalPhysical.lean; sha256: 4edf2a572e98c3b7e0bd7b0144a82c3103fd07c7c8800d5de2a30d44653318b7 -/
section Source1912
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondNonexceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

lemma paired_sqrt (A E₁ E₂ c d:ℝ) (hA:0≤A) (hE₁:0≤E₁) (hE₂:0≤E₂)
    (hc:0<c) (_hd:0<d) :
    Real.sqrt (A*E₁/c)*Real.sqrt (A*E₂/d)=A/Real.sqrt (c*d)*Real.sqrt (E₁*E₂) := by
  rw [←Real.sqrt_mul (div_nonneg (mul_nonneg hA hE₁) hc.le)]
  rw [show A*E₁/c*(A*E₂/d)=A^2*(E₁*E₂)/(c*d) by ring]
  rw [Real.sqrt_div (mul_nonneg (sq_nonneg A) (mul_nonneg hE₁ hE₂)),
    Real.sqrt_mul (sq_nonneg A),Real.sqrt_sq hA]
  ring

omit [DecidableEq ι] in
theorem paired_core_budget (s:Input ι) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (Ce Z δ E₁ E₂ t:ℝ) (hCe:0≤Ce) (hZ:0≤Z) (hE₁:0≤E₁) (hE₂:0≤E₂)
    (J₁ J₂:ℕ) :
    windowBudget J₁ t (core s C Ce Z δ E₁)*windowBudget J₂ t (core s D Ce Z δ E₂)=
      (Ce*Z^δ*profileCost s*volume s.toData)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
        Real.sqrt (E₁*E₂)*heightEnvelope t^(J₁+J₂)*profileMoment J₁*profileMoment J₂ := by
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hA:0≤Ce*Z^δ*profileCost s*volume s.toData:=by
    exact mul_nonneg (mul_nonneg (mul_nonneg hCe (Real.rpow_nonneg hZ _)) (profileCost_nonneg s)) (volume_pos s.toData).le
  have he (G:Ideal O) (E:ℝ):core s G Ce Z δ E=
      (Ce*Z^δ*profileCost s*volume s.toData)*E/(G.absNorm:ℝ):=by
    unfold core volume
    ring
  rw [he C E₁,he D E₂]
  simp only [windowBudget,pow_add]
  have hh:=paired_sqrt _ E₁ E₂ _ _ hA hE₁ hE₂ hc hd
  calc
    _=(Real.sqrt (_*E₁/(C.absNorm:ℝ))*Real.sqrt (_*E₂/(D.absNorm:ℝ)))*
      (heightEnvelope t^J₁*heightEnvelope t^J₂)*profileMoment J₁*profileMoment J₂:=by ring
    _=_:=by rw [hh]

theorem actual_physical_from_supported_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0 Ce:ℝ,0<C0 ∧ 0<Ce ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Kphys:ℝ,0<Kphys → ∀n:Fin 4→ℤ,
      let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (s:Input ι),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀Hsource:ℝ,(∀I,β I≠0→(I.absNorm:ℝ)≤Hsource) →
      Hsource/(D.absNorm:ℝ)≤Z^B →
      ∀(R:ℝ) (rows:Finset O),
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),∀hH:0<H,
      ∀hΦ:(∀z:O,0≤(Φ (normValue z/H)).re), (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤E₂*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock η t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        (C0*Ce)*Z^(2*δ)*profileCost s*(outerScalar C D Kphys n*normalizer C D U)/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(1+r)^decay := by
  obtain ⟨C0,Ce,hC0,hCe,hkernel⟩:=actual_block_from_supported_children lo hi W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,Ce,hC0,hCe,?_⟩
  filter_upwards [hkernel] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n r η τ t s hlo hhi R0 seed S β C D hC hD hsC hsD hnC hnD hCD U A hτ Hsource hβ hn
    R rows Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hr:0<r:=div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hpow:0<(1+r)^decay:=pow_pos (by linarith) _
  have hh:=hZ.2 r hr η τ t s hlo hhi R0 seed C D hC hD hsC hsD hnC hnD hCD U hτ Hsource hβ hn
    R rows (fun _=>Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1)))
    (dyadicScale (n 2)) (dyadicScale (n 3)) (dyadicScale_pos _) (dyadicScale_pos _)
    Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  change (1+r)^decay*‖normalizedBlock η t S β C D hC hD U R rows W Kphys n‖≤_ at hh
  rw [paired_core_budget s C D hC hD Ce Z δ E₁ E₂ t hCe.le
    (zero_lt_one.trans hZ.1).le hE₁ hE₂ J₁ J₂] at hh
  have ho:0≤outerScalar C D Kphys n:=by unfold outerScalar;positivity
  have hno:0≤normalizer C D U:=(normalizer_pos C D hC U).le
  have hnrows:∀z∈rows,z≠0:=fun z hz=>(hrows z hz).1
  have hp:=mul_le_mul_of_nonneg_left hh (mul_nonneg ho hno)
  have hphys:‖physicalBlock η t S β C D hC hD U R rows W Kphys n‖=
      outerScalar C D Kphys n*normalizer C D U*
        ‖normalizedBlock η t S β C D hC hD U R rows W Kphys n‖:=by
    rw [physicalBlock_eq η t S β C D hC hD U R rows hnrows W Kphys hKphys n,
      norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno]
  rw [hphys]
  apply (div_le_iff₀ (volume_pos s.toData)).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpow).mpr
  have hzz:Z^(2*δ)=Z^δ*Z^δ:=by
    rw [show 2*δ=δ+δ by ring,Real.rpow_add (zero_lt_one.trans hZ.1)]
  rw [hzz]
  convert hp using 1 <;> ring

end SevenEighths.CenteredMomentSecondNonexceptionalPhysical

end

end OAI

end Source1912

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondActivePhysicalDictionary.lean; sha256: fe9c129df5882d8d23b2cd568f9fd1ab3815dcb895b5cffc4b49e8f6a340c0c0 -/
section Source1913
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondActivePhysicalDictionary
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorColumns
open CenteredMomentSecondSectorFrequency CenteredMomentActiveSource
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentSecondWholeKernel CenteredMomentLogDyadic
open CenteredMomentSecondSectorRetained CenteredMomentSmooth
local notation "O"=>HeckeFamily.O

 theorem sectorPool_active (C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(β:Ideal O→ℂ):
    sectorPool C hC (activeSource S β)=(sectorPool C hC S).filter (fun I=>β (C*I)≠0):=by
  ext I
  simp only [sectorPool,Finset.mem_filter,mem_residualPool,supportedColumns_active]
  tauto

 theorem sector_sum_active (C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(β f:Ideal O→ℂ)
    (hf:∀I,β (C*I)=0→f I=0):
    (∑I∈sectorPool C hC (activeSource S β),f I)=∑I∈sectorPool C hC S,f I:=by
  rw [sectorPool_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h:β (C*I)=0
  · simp only [h,ne_eq,not_true_eq_false,ite_false,hf I h]
  · simp only [h,ne_eq,not_false_eq_true,ite_true]

 theorem sector_pair_sum_active (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(f:Ideal O→Ideal O→ℂ)
    (hleft:∀I J,β (C*I)=0→f I J=0)(hright:∀I J,β (D*J)=0→f I J=0):
    (∑I∈sectorPool C hC (activeSource S β),∑J∈sectorPool D hD (activeSource S β),f I J)=
      ∑I∈sectorPool C hC S,∑J∈sectorPool D hD S,f I J:=by
  simp_rw [sector_sum_active D hD S β _ (fun J h=>hright _ J h)]
  apply sector_sum_active C hC S β
  intro I h
  exact Finset.sum_eq_zero (fun J hJ=>hleft I J h)

 theorem sectorFrequency_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(F:O→Ideal O→Ideal O→ℂ)(z:O):
    sectorFrequency η t S β C D hC hD F z=
      sectorFrequency η t (activeSource S β) β C D hC hD F z:=by
  let f:Ideal O→Ideal O→ℂ:=fun I J=>
    if hI:Supported (C*I) then if hJ:Supported (D*J) then
      (if IsCoprime I J then idealCorrelation (C*I) (D*J) hI hJ z else 0)*
        ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*F z I J
      else 0 else 0
  have he (T:Finset (Ideal O)):
      sectorFrequency η t T β C D hC hD F z=
        ∑I∈sectorPool C hC.1 T,∑J∈sectorPool D hD.1 T,f I J:=by
    calc
      _=∑I:sectorPool C hC.1 T,∑J:sectorPool D hD.1 T,f I J:=by
        unfold sectorFrequency
        apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro J hJ
        have hc:Supported (C*I):=(supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 T I⟩
        have hd:Supported (D*J):=(supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 T J⟩
        simp only [f,dite_eq_left hc,dite_eq_left hd]
      _=_:=by
        simp_rw [Finset.sum_coe_sort]
        exact Finset.sum_coe_sort (sectorPool C hC.1 T)
          (fun I=>∑J∈sectorPool D hD.1 T,f I J)
  rw [he S,he (activeSource S β)]
  symm
  apply sector_pair_sum_active C D hC.1 hD.1 S β f
  · intro I J h
    simp only [f,h,zero_mul,mul_zero]
    split_ifs <;> rfl
  · intro I J h
    simp only [f,h,zero_mul,star_zero,mul_zero]
    split_ifs <;> rfl

 theorem physicalBlock_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t (activeSource S β) β C D hC hD U R rows W K n:=by
  unfold physicalBlock
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  exact sectorFrequency_active η t S β C D hC hD
    (fun j I J=>physicalKernel C D W K R j I J*
      ((dyadicWeight (n 0) (secondEffectiveScale C D
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K)*
        dyadicWeight (n 1) (normValue z)*dyadicWeight (n 2) (I.absNorm:ℝ)*
        dyadicWeight (n 3) (J.absNorm:ℝ):ℝ):ℂ)) _

 theorem normalizedBlock_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    normalizedBlock η t S β C D hC hD U R rows W K n=
      normalizedBlock η t (activeSource S β) β C D hC hD U R rows W K n:=by
  unfold normalizedBlock
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  exact sectorFrequency_active η t S β C D hC hD
    (fun _ I J=>wholeKernel W (fun _=>logAnnulus)
      (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
      (Real.log (secondEffectiveScale C D
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/dyadicScale (n 0)))
      (Real.log (normValue z/dyadicScale (n 1)))
      (Real.log ((I.absNorm:ℝ)/dyadicScale (n 2)))
      (Real.log ((J.absNorm:ℝ)/dyadicScale (n 3)))) _

end SevenEighths.CenteredMomentSecondActivePhysicalDictionary

end

end OAI

end Source1913

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondEnergySplit.lean; sha256: 851946cecb6d17f13253c85b4edc366c20ef4cd755d27523e85a06a968266960 -/
section Source1914
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondEnergySplit
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentRestrictedEnergy
open CenteredMomentChildRows RayFourExpansion
local notation "O"=>HeckeFamily.O

lemma physicalBlock_filter_split (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)(p:O→Prop):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (rows.filter p) W K n+
      physicalBlock η t S β C D hC hD U R (rows.filter (fun z=>¬p z)) W K n:=by
  unfold physicalBlock
  exact (Finset.sum_filter_add_sum_filter_not rows p _).symm

def sourceRows (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):Finset O:=
  liveRows C D U R (retainedRows R (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))

lemma sourceRows_nonzero (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)
    (z:O)(hz:z∈sourceRows C D U R):z≠0:=
  (liveRows_geometry C D U R _ z hz).2.1

def partRows (exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):Finset O:=
  (sourceRows C D U R).filter (fun z=>if exceptional then
    CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z
    else nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z)

lemma partRows_false (η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):
    partRows false η χ Q m C D U R=(sourceRows C D U R).filter (fun z=>
      ¬CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z):=by
  ext z
  simp only [partRows,Bool.false_eq_true,ite_false,Finset.mem_filter,nonexceptional]
  exact ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,sourceRows_nonzero C D U R z h.1,h.2⟩⟩

def partEnergy (exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ):ℂ:=
  ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          W K (fun i=>(n i:ℤ))

theorem original_energy_split (η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ)(hK:0<K)
    (hH:∀I∈S,β I≠0→(I.absNorm:ℝ)≤H):
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      partEnergy true η χ Q m t S β W K Tsec Z ξ H+
      partEnergy false η χ Q m t S β W K Tsec Z ξ H:=by
  rw [original_live_blocks η t S β W K Tsec Z ξ H hK hH]
  unfold partEnergy
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [partRows_false]
  exact physicalBlock_filter_split η t (activeSource S β) β p.val.1 p.val.2 _ _ U
    (frequencyRadius Tsec Z ξ) (sourceRows p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ)) W K _ _

theorem partEnergy_norm_le (exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ):
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖≤
  ∑p∈liveLabels η S β,
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          W K (fun i=>(n i:ℤ))‖
 :=by
  unfold partEnergy
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    (common_height_norm_le_one η t _ _
      (commonLabels_supported (activeSource S β) _ _ p.property).1.1
      (commonLabels_supported (activeSource S β) _ _ p.property).2.1)).trans
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro U hU
  exact norm_sum_le _ _

end SevenEighths.CenteredMomentSecondEnergySplit

end

end OAI

end Source1914

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondNonexceptionalChosenBlock.lean; sha256: 0655b33a03da38cac8474be96737daee0232c099f22c86c6f886c62a33966007 -/
section Source1915
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair

def canonicalRadial (τ:Character)(Q:Ideal O)(n:Fin 4→ℤ):Radial:=
  sourceRadial (fun z=>z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow τ Q fixedBadMask 1 z)
    ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=>ballProfile_nonneg _)

lemma sourceRadial_eq_canonical {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (hm:m≠0)(hml:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)(n:Fin 4→ℤ):
    sourceRadial (nonexceptional η χ Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))
      ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=>ballProfile_nonneg _)=
      canonicalRadial (τ χ) Q n:=by
  have he:nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)=
      (fun z=>z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z):=by
    funext z
    exact propext (h.nonexceptional_iff χ Q m z hm hml hm2)
  simp only [canonicalRadial,he]

theorem actual_canonical_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0 Ce:ℝ,0<C0 ∧ 0<Ce ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Kphys:ℝ,0<Kphys → ∀n:Fin 4→ℤ,
      let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
      ∀(s:Input ι) (τ:RayCharacter→Character),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let _A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      Family s.η C D hC hD U τ →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      ∀R:ℝ,
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₂*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock s.η s.t S β C D hC hD U R
        (partRows false s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        (C0*Ce)*Z^(2*δ)*profileCost s*(outerScalar C D Kphys n*normalizer C D U)/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(1+r)^decay :=by
  obtain ⟨C0,Ce,hC0,hCe,hbound⟩:=
    CenteredMomentSecondNonexceptionalPhysical.actual_physical_from_supported_children
      lo hi W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,Ce,hC0,hCe,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n r s τ hlo hhi R0 seed S β C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH R Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂ hleft hright
  let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  let rows:=partRows false s.η χ₀ Q m C D U R
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤sourceRadius s:=by
    intro I hi
    exact (original_column_norm s R0 seed I hz1 hz2 hi).2
  have hHD:sourceRadius s/(D.absNorm:ℝ)≤Z^B:=by
    have hDN:1≤(D.absNorm:ℝ):=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
    by_cases hp:0≤sourceRadius s
    · exact (div_le_self hp hDN).trans hH
    · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hp) (Nat.cast_nonneg _)).trans
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  have hrows:∀z∈dyadicRows rows n,nonexceptional s.η χ₀ Q m A z:=by
    intro z hz
    have hh:=Finset.mem_filter.mp ((dyadicRows_subset rows n) hz)
    simpa only [rows,partRows,Bool.false_eq_true,ite_false] using hh.2
  have hmajor:∀z∈dyadicRows rows n,1≤(ballProfile (normValue z/dyadicScale (n 1))).re:=by
    intro z hz
    have hb:=ballProfile_majorizes (dyadicScale (n 1)) (dyadicScale_pos _) z
      (dyadicRows_norm rows n z hz).2.le
    simpa only [normValue_eq_embedding] using hb
  have hleft':∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
      ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
        (sourceRadial (nonexceptional s.η χ Q m A) ballProfile (dyadicScale (n 1))
          (dyadicScale_pos _) (fun z=>ballProfile_nonneg _)) L a≤E₁*(1+‖v‖)^(2*J₁):=by
    intro L hL hLN hsf χ v b a ha
    rw [sourceRadial_eq_canonical hf χ Q m hm hml hm2 n]
    exact hleft L hL hLN hsf χ v b a ha
  have hright':∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
      ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
        (sourceRadial (nonexceptional s.η χ Q m A) ballProfile (dyadicScale (n 1))
          (dyadicScale_pos _) (fun z=>ballProfile_nonneg _)) L a≤E₂*(1+‖v‖)^(2*J₂):=by
    intro L hL hLN hsf χ v b a ha
    rw [sourceRadial_eq_canonical hf χ Q m hm hml hm2 n]
    exact hright L hL hLN hsf χ v b a ha
  have hh:=hZ.2 Kphys hKphys n s.η τ s.t s hlo hhi R0 seed C D hC hD hsC hsD hNC hND hCD U
    hf.height_eq (sourceRadius s) hβ hHD R (dyadicRows rows n) Q m χ₀ hQ hml hm2 hrows
    ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun z=>ballProfile_nonneg _) hmajor
    E₁ E₂ hE₁ hE₂ hleft' hright'
  rwa [←physicalBlock_dyadic_rows] at hh

end SevenEighths.CenteredMomentSecondNonexceptionalChosenBlock

end

end OAI

end Source1915

/- Original source: OAI/NumberTheory/DirichletL/Energy/ChildState.lean; sha256: 62e84ccaf59e12bc795d884d473cdeb450a83f5f9588144bb4a420ae7af44c65 -/
section Source1916
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyChildState
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentEnergyState CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondDyadicRowSupport CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O

lemma ball_support : Function.support (ballProfile:ℝ→ℂ)⊆Set.Iic (2:ℝ):=by
  intro x hx
  by_cases h:0≤x
  · exact (CenteredMomentAmplifiedRetainedRadius.ballProfile_support_upper x h hx).le
  · exact (lt_of_not_ge h).le.trans (by norm_num)

lemma canonical_mask_nonexceptional (τ:Character)(Q R:Ideal O)(hR:R≠0)
    (n:Fin 4→ℤ)(z:O)(hz:(canonicalRadial τ Q n).keep z):
    ¬CenteredExceptionalProfile.FixedInducingRow τ Q
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z:=by
  intro hh
  exact hz.2 ((CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff τ Q
    fixedBadMask (ConcretePrimeRowBridge.idealGenerator R) 1 z fixedBadMask_ne_zero
    (ConcretePrimeRowBridge.idealGenerator_ne_zero R hR) one_ne_zero hz.1
    (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hh)

def canonicalState (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)
    (hn:1≤dyadicScale (n 1)):NaturalState Z Bmask 2 where
  character:=τ
  fixedModulus:=Q
  puncture:=R
  radial:=canonicalRadial τ Q n
  rowWidth:=Real.logb Z (dyadicScale (n 1))
  characterWidth:=Real.logb Z (τ.modulus.absNorm:ℝ)
  base_ge_one:=hZ.le
  row_nonneg:=Real.logb_nonneg hZ hn
  character_nonneg:=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))
  scale_eq:=(Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _)).symm
  modulus_bound:=by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  puncture_ne_zero:=hR
  puncture_bound:=hRN
  radial_support:=ball_support
  row_ne_zero:=fun _ hz=>hz.1
  nonexceptional:=canonical_mask_nonexceptional τ Q R hR n

lemma canonicalState_width (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)(hn:1≤dyadicScale (n 1)):
    (canonicalState Z Bmask hZ τ Q R hR hRN n hn).width=
      Real.logb Z (dyadicScale (n 1))+Real.logb Z (τ.modulus.absNorm:ℝ):=rfl

lemma canonicalState_power (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)(hn:1≤dyadicScale (n 1)):
    Z^(canonicalState Z Bmask hZ τ Q R hR hRN n hn).width=
      (τ.modulus.absNorm:ℝ)*dyadicScale (n 1):=by
  rw [canonicalState_width,Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  ring

lemma common_puncture_bound (Z Bmask Bsource:ℝ)(hZ:0<Z)(R C:Ideal O)
    (hR:(R.absNorm:ℝ)≤Z^Bmask)(hC:(C.absNorm:ℝ)≤Z^Bsource):
    ((R*C).absNorm:ℝ)≤Z^(Bmask+Bsource):=by
  rw [map_mul,Nat.cast_mul,Real.rpow_add hZ]
  exact mul_le_mul hR hC (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)

section Actual
variable {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
  {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
  (h:Family η C D hC hD U τ)
  (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
  (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
  (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)

include hne in

lemma actual_dyad_ge_one : 1≤dyadicScale (n 1):=by
  obtain ⟨z,_,hz,hz0,_⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U
    radius rows W K n hne
  exact (normValue_ge_one z hz0).trans (dyadicRows_norm rows n z hz).2.le

def actualState (Z Bmask:ℝ)(hZ:1<Z)(χ:RayCharacter)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask):NaturalState Z Bmask 2:=
  canonicalState Z Bmask hZ (τ χ) Q R hR hRN n
    (actual_dyad_ge_one t S β radius rows W K n hne)

include h hK in

theorem actualState_width (Z Bmask:ℝ)(hZ:1<Z)(χ:RayCharacter)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask):
    (actualState (τ:=τ) t S β radius rows W K n hne Z Bmask hZ χ Q R hR hRN).width≤
      Real.logb Z radius+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)):=by
  exact dyadic_log_budget h t S β radius rows W K hK n hne Z hZ χ

end Actual
end SevenEighths.CenteredMomentEnergyChildState

end

end OAI

end Source1916

/- Original source: OAI/NumberTheory/DirichletL/Energy/AllocatedChildren.lean; sha256: 4e5de51d8260988b9fa03df021978469a2886c00f7ac20b0c2d1a3d44435d4d8 -/
section Source1917
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedChildren
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentDetectorDictionary CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentSecondHeightFamily CenteredMomentHeckeHeight
open CenteredMomentOriginalRadialComparison CenteredMomentInductionEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

lemma natural_product_eq_positive {η:Character}{z:O}(F:NaturalRow η z)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i,0<P i):
    polynomial F.character false W₁ X₁ 0 0*polynomial F.character false W₂ X₂ 0 0*
      ∏i,naturalSlot F.character (pool i) (β i) (P i)=
      CenteredMomentRetainedEnergy.positiveSlotRow η
        (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 z
        W₁ W₂ pool β P 0 X₁ X₂:=by
  rw [natural_unit_mask_positive F]
  have hh:=positiveSlotRow_eq_product η F.character fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) W₁ W₂ pool β P X₁ X₂ 0 0 hX₁ hX₂ hP
  rw [twistProfile_zero,twistProfile_zero] at hh
  rw [hh]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hs:=CenteredMomentRayMaskedFloor.natural_slot_eq F (pool i) (β i) (P i) 0
  have he:heightCoefficient (β i) 0=β i:=by
    funext I
    simp only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]
  rw [he] at hs
  exact hs

lemma natural_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i,0<P i):
    radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
      polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
      ∏i,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
      r.keep r.profile r.scale=
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 W₁ W₂ pool β P
      X₁ X₂ r.keep r.profile r.scale:=by
  unfold radialEnergy CenteredMomentInductionEnergy.energy
  apply tsum_congr
  intro z
  by_cases hk:r.keep z
  · simp only [ite_eq_left hk,naturalCharacter_eq η z (hz z hk)]
    rw [natural_product_eq_positive (naturalRow η z (hz z hk)) W₁ W₂ pool β P X₁ X₂ hX₁ hX₂ hP]
  · simp only [ite_eq_right hk]

omit [Fintype α] in
lemma natural_subset_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (F:Finset α)(W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i∈F,0<P i):
    radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
      polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
      ∏i∈F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
      r.keep r.profile r.scale=
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 W₁ W₂
      (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂ r.keep r.profile r.scale:=by
  have hh:=natural_radial_eq_energy (α:=F) η r hz W₁ W₂
    (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂ hX₁ hX₂
    (fun i=>hP i i.property)
  have hp (z:O):(∏i:F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))=
      ∏i∈F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i):=
    Finset.prod_coe_sort F (fun i:α=>naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
  simp_rw [hp] at hh
  exact hh

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentRetainedProfile CenteredMomentCommonAllocationSum

def allocatedEnergy (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2))) (V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O))(J:Finset α):ℝ:=
  CenteredMomentInductionEnergy.energy (ι := ↥(liveIndices D a\J)) η
    (fixedBadMask*ConcretePrimeRowBridge.idealGenerator (1:Ideal O)) 1 0
    (V₁.profile (rawScale D a X₁ 0) (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile (rawScale D a X₂ 1) (rawScale_pos D a X₂ hX₂ 1) t)
    (fun i:↥(liveIndices D a\J)=>pool i) (fun i:↥(liveIndices D a\J)=>heightCoefficient (β i) t)
    (fun i:↥(liveIndices D a\J)=>P i)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    r.keep r.profile r.scale

lemma child_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (D:Ideal O)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))) (V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O))(J:Finset α)
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0):
    radialEnergy (fun z=>child (α:=α) (naturalCharacter η z) D a V₁ V₂ pool β P
      t X₁ X₂ hX₁ hX₂ D₁ D₂ J) r.keep r.profile r.scale=
      allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ J:=by
  have hd₁:0<(Ideal.absNorm (∏I∈D₁,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₁))
  have hd₂:0<(Ideal.absNorm (∏I∈D₂,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₂))
  exact natural_subset_radial_eq_energy η r hz (liveIndices D a\J)
    (V₁.profile (rawScale D a X₁ 0) (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile (rawScale D a X₂ 1) (rawScale_pos D a X₂ hX₂ 1) t)
    pool (fun i=>heightCoefficient (β i) t) P
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    (div_pos (by unfold clippedScale;positivity) hd₁)
    (div_pos (by unfold clippedScale;positivity) hd₂) (fun i _=>hP i)

def commonAllocatedEnergy (s:Input α)(τ:Character)(v:ℝ)(C R:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂:Plain)(r:Radial)(left:Bool)(D₁ D₂:Finset (Ideal O))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)):ℝ:=
  let d:=commonData (withHeight s τ v) C R B
  if left then allocatedEnergy τ r D a V₁ V₂ d.slots d.coefficient d.P
    v d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J
  else allocatedEnergy τ r D a V₁ V₂ d.slots d.coefficient d.P
    v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J

lemma commonChild_energy (s:Input α)(τ:Character)(v:ℝ)(C R:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂:Plain)(r:Radial)(hz:∀z,r.keep z→z≠0)(left:Bool)(D₁ D₂:Finset (Ideal O))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0):
    radialEnergy (fun z=>commonChild s τ v C R B D a V₁ V₂ left z D₁ D₂ J)
      r.keep r.profile r.scale=commonAllocatedEnergy s τ v C R B D a V₁ V₂ r left D₁ D₂ J:=by
  let d:=commonData (withHeight s τ v) C R B
  cases left
  · exact child_radial_eq_energy τ r hz D a V₁ V₂ d.slots d.coefficient d.P d.P_pos
      v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J hD₁ hD₂
  · exact child_radial_eq_energy τ r hz D a V₁ V₂ d.slots d.coefficient d.P d.P_pos
      v d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J hD₁ hD₂

end SevenEighths.CenteredMomentEnergyAllocatedChildren

end

end OAI

end Source1917

/- Original source: OAI/NumberTheory/DirichletL/Energy/AllocatedBound.lean; sha256: 94936519cab549b89f05979b9efa635c3c7b02beb6d264983c040df502a8140b -/
section Source1918
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedChildren
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentNaturalRowSource CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

theorem actual_common_from_energy (b M:α→ℝ)(hM:∀i,0≤M i)(ε:ℝ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀s:Input α,(∀i,s.hi i≤b i)→(∀i,s.M i≤M i)→
    ∀(τ:Character)(v:ℝ)(C R:Ideal O),R≠0→∀B:actualAllocations s.pools C,
    ∀(L:Ideal O)(a:Allocation L (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂:Plain,V₁.W=s.W₁→V₂.W=s.W₂→∀r:Radial,(∀z,r.keep z→z≠0)→
    ∀E₁ E₂:ℝ,0≤E₁→0≤E₂→
    (∀left:Bool,∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
      ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      commonAllocatedEnergy s τ v C R B L a V₁ V₂ r left D₁ D₂ J≤(if left then E₁ else E₂))→
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂):=by
  obtain ⟨C₀,hC₀,hbound⟩:=actual_common_radial_energy b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hz E₁ E₂ hE₁ hE₂ he
  apply hbound s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hz E₁ E₂ hE₁ hE₂
  · intro D₁ hD₁ D₂ hD₂ J hJ
    rw [commonChild_energy s τ v C R B L a V₁ V₂ r hz true D₁ D₂ J
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₁) hi)).ne_zero)
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₂) hi)).ne_zero)]
    exact he true D₁ hD₁ D₂ hD₂ J hJ
  · intro D₁ hD₁ D₂ hD₂ J hJ
    rw [commonChild_energy s τ v C R B L a V₁ V₂ r hz false D₁ D₂ J
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₁) hi)).ne_zero)
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₂) hi)).ne_zero)]
    exact he false D₁ hD₁ D₂ hD₂ J hJ

end SevenEighths.CenteredMomentEnergyAllocatedChildren

end

end OAI

end Source1918

/- Original source: OAI/NumberTheory/DirichletL/Energy/AllocatedProfiles.lean; sha256: e72bcb1dc265f756946435a977c11e578b701c34f673b9ca24a8bc0a1f3ec5ee -/
section Source1919
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedProfiles
open CenteredMomentFiniteProfileExceptional

def retainedPair (a b:ℝ)(ha:0<a)(p:Profiles a b)
    (U:Fin 2→ℝ)(hU:∀i,0<U i)(t:ℝ):Profiles (a/max 1 b) b where
  profile:=fun i=>(sourcePlain a b ha (p.profile i) (p.support i)).profile (U i) (hU i) t
  support:=fun i=>sourcePlain_support a b ha (p.profile i) (p.support i) (U i) (hU i) t

theorem retained_pair_control (a b:ℝ)(ha:0<a)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀p:Profiles a b,∀U:Fin 2→ℝ,∀hU:∀i,0<U i,∀t:ℝ,
      (retainedPair a b ha p U hU t).control S≤
        C*p.control T*(1+‖t‖)^(2*n):=by
  obtain ⟨n,T,C,hC,hbound⟩:=plain_profile_source_control a b ha S
  refine ⟨n,T,C^2,sq_pos_of_pos hC,?_⟩
  intro p U hU t
  have h₀:=hbound (p.profile 0) (p.support 0) (U 0) (hU 0) t
  have h₁:=hbound (p.profile 1) (p.support 1) (U 1) (hU 1) t
  have hp₀:=sourceControl_nonneg T (p.profile 0)
  change sourceControl S _*sourceControl S _≤_
  apply (mul_le_mul h₀ h₁ (sourceControl_nonneg _ _) (by positivity)).trans_eq
  simp only [Profiles.control,show 2*n=n+n by omega,pow_add]
  ring

end SevenEighths.CenteredMomentEnergyAllocatedProfiles

end

end OAI

end Source1919
