import OpenAIGrouped.Unit024
import OpenAIGrouped.Unit016
import OpenAIGrouped.Unit020
import OpenAIGrouped.Unit022
import OpenAIGrouped.Unit008
import OpenAIGrouped.Unit017
import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit009
import OpenAIGrouped.Unit015
import OpenAIGrouped.Unit021
import OpenAIGrouped.Unit018
import OpenAIGrouped.Unit012
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import OpenAIGrouped.Unit007
import OpenAIGrouped.Unit013

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceInputFirstSectorTailNatural.lean; sha256: be43df7003d195e02578dcbb58858fe7a770b6e799f3757e3841af034f2801c5 -/
section Source1000
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
open CenteredMomentSourceInputTailUniform CenteredMomentFirstTailAggregate
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
theorem local_input_tail (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),
      0<K→volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K (volume s.toData) Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  obtain ⟨S,C,hC,htail⟩ := local_input_tail_arbitrary_saving hi wlo whi (3*B) ξ saving
    hhi hwlo hwhi (by positivity) hξ
  refine ⟨S,C,hC,?_⟩
  filter_upwards [htail] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK hV hKi
  have hz : 0<Z := zero_lt_one.trans hZ.1
  have hV0 : 0<volume s.toData := volume_pos s
  have hVcap : volume s.toData≤Z^(3*B) := hV.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))
  have hTcap : (volume s.toData)^2/K≤Z^(3*B) := by
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hV0.le hV 2) hKi (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num
    ring
  exact hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K _ hK hVcap hTcap le_rfl

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI

end Source1000

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceInputFirstRemainder.lean; sha256: 6d0c7861e39c3d9c0435105f7fd8c1e88eccc9c4346f07414582c169fa356c23 -/
section Source1001
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstRemainder
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentSourceInputZeroUniform CenteredMomentSourceInputFirstSectorTail
open CenteredMomentFirstEnergy EisensteinSchwartzPoisson
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
theorem original_first_remainder (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(m A:O),ConcretePrimeRowBridge.goodLambda∣m→(2:O)∣m→
      ∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s R seed) Φ K-
        CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K
          (volume s.toData) Z ξ‖/volume s.toData≤
      Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
      Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Sdiag,Cdiag,hCdiag,hdiag⟩:=first_input_zero_capped hi wlo whi B ε hhi hwlo hwhi hB hε
  obtain ⟨Stail,Ctail,hCtail,htail⟩:=local_input_tail hi wlo whi B ξ saving hhi hwlo hwhi hB hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,?_⟩
  filter_upwards [htail] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have hd:=hdiag Z hZ.1.le s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hVcap m A R seed Φ K hK.le
  have ht:=hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK hVcap hKi
  rw [CenteredMomentFirstSectorLocalization.finiteHeckeEnergy_sector_localized
    s.η m A s.t hml hm2 (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s R seed) Φ K (volume s.toData) Z ξ hK]
  rw [show ∀a b c:ℂ,a+b+c-b=a+c by intros;ring]
  exact ((div_le_div_of_nonneg_right (norm_add_le _ _) (volume_pos s).le).trans_eq
    (add_div _ _ _)).trans (add_le_add hd ht)

end SevenEighths.CenteredMomentSourceInputFirstRemainder

end

end OAI

end Source1001

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSourceReduction.lean; sha256: 59a7e36035cf4db59dc5deb5f17ed986ea267f4367117e7520f86e003d1919bb -/
section Source1002
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSourceReduction
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentSourceInputFirstRemainder CenteredMomentFirstRetainedNorm
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors CenteredMomentFirstEnergy
open CenteredMomentActiveSource (activeSource)
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def physicalMass (s:Input ι)(R seed:Ideal O)(m A:O)(Φ:𝓢(ℝ,ℂ))(K Z ξ:ℝ):ℝ:=
  let β:=coefficient s R seed
  let T:=activeSource (finiteColumns (Fintype.piFinset s.pools)) β
  ∑p:commonLabels (supportedColumns T) (supportedColumns T),
    sectorMass s R seed m A s.t T p.val.1 p.val.2
      (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
      (volume s.toData) Z ξ

 theorem original_first_physical_reduction (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(m A:O),ConcretePrimeRowBridge.goodLambda∣m→(2:O)∣m→
      ∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s R seed) Φ K‖/volume s.toData≤
      physicalMass s R seed m A Φ K Z ξ/volume s.toData+
      Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
      Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,hrem⟩:=
    original_first_remainder hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,?_⟩
  filter_upwards [hrem] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have hz (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hr:=original_retained_norm s R seed (he₁.symm ▸ hz W₁ hs₁) (he₂.symm ▸ hz W₂ hs₂)
    m A s.t (finiteColumns (Fintype.piFinset s.pools)) Φ K (volume s.toData) Z ξ hK
  change ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K
      (volume s.toData) Z ξ‖≤physicalMass s R seed m A Φ K Z ξ at hr
  have he:=hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have htri:=norm_le_norm_sub_add
    (finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K)
    (CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K (volume s.toData) Z ξ)
  have hdiv:=div_le_div_of_nonneg_right htri (volume_pos s).le
  rw [add_div] at hdiv
  have hrdiv:=div_le_div_of_nonneg_right hr (volume_pos s).le
  linarith

end SevenEighths.CenteredMomentFirstSourceReduction

end

end OAI

end Source1002

/- Original source: OAI/NumberTheory/DirichletL/Moments/TerminalEnergy.lean; sha256: c02686ff8055b93c8ef8dada9efaf0c072703e34346c15c91e8b02fb26d057b7 -/
section Source1003
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentTerminalEnergy
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O

theorem actual_small_width_source_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple J)) (Z mExp q M AExp ρ δ : ℝ),1≤Z →
      0≤mExp → 0≤q → mExp+q=M → M≤ρ → AExp≤M+δ →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      H=Z^AExp →
      ‖finiteHeckeEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J=>ν j.val)
          (fun j : J=>Wslot j.val) (fun j : J=>P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ (Z^mExp)‖/H≤C*Z^(M+ρ+δ) := by
  obtain ⟨C,hC,hbound⟩ := smooth_subset_source_absolute_energy F Wslot W₁ W₂ Φ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Z mExp q M AExp ρ δ hZ hm hq hM hsmall hA H hscale
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  have hh := (hbound J hJ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S (Z^mExp) (Real.rpow_pos_of_pos hZ0 _)).2
  change _≤C*max 1 (Z^mExp)*H at hh
  rw [max_eq_right (Real.one_le_rpow hZ hm),hscale] at hh
  apply hh.trans
  rw [mul_assoc,←Real.rpow_add hZ0]
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le hZ
  linarith

end SevenEighths.CenteredMomentTerminalEnergy

end

end OAI

end Source1003

/- Original source: OAI/NumberTheory/DirichletL/Moments/UncenteredTerminal.lean; sha256: 43222cac725b6b4e8f2300bd2e1d3b5e54eb8d388ee899462a06037ddbd78d28 -/
section Source1004
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentUncenteredTerminal
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

def uncenteredProfileCoefficient {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))*
    (if IsCoprime (finiteTupleProduct v) R then 1 else 0)*
    (W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/X₁)*
      W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/X₂))*
    (if s∣finiteTupleProduct v then 1 else 0)

def comparisonScale (b : ℝ) : ℝ := 1/(2*max 1 b)

lemma comparisonScale_pos (b : ℝ) : 0<comparisonScale b := by
  have hb : 0<max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  unfold comparisonScale
  positivity

lemma comparison_product (b T : ℝ) : comparisonScale b*(T/comparisonScale b)=T := by
  have hy := (comparisonScale_pos b).ne'
  field_simp

theorem comparison_first_zero (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (B I : Ideal O) (hB : B≠0) :
    W ((Ideal.absNorm (B*I):ℝ)/comparisonScale b)=0 := by
  by_contra h
  have ht := hs h
  by_cases hI : I=0
  · simp only [hI,mul_zero,map_zero,Nat.cast_zero,zero_div,Set.mem_Icc] at ht
    linarith [ht.1]
  have hn : 1≤(Ideal.absNorm (B*I):ℝ) :=
    QuadraticMainBoundary.norm_one_le (mul_ne_zero hB hI)
  have hmax : 1≤max 1 b := le_max_left _ _
  have hb : b≤max 1 b := le_max_right _ _
  have harg : (Ideal.absNorm (B*I):ℝ)/comparisonScale b=
      (Ideal.absNorm (B*I):ℝ)*(2*max 1 b) := by
    simp [comparisonScale,div_eq_mul_inv]
  rw [harg] at ht
  have hupper := ht.2
  nlinarith

theorem profileCoefficient_eq_uncentered {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ : ℝ) (ha₁ : 0<a₁)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (X₁ X₂ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (hB₁ : B₁≠0) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ (comparisonScale b₁) Y₂ B₁ B₂ s=
      uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ B₁ B₂ s := by
  funext v
  simp only [profileCoefficient,idealRectangle,
    comparison_first_zero W₁ a₁ b₁ ha₁ hs₁ B₁ (v (Sum.inr 0)) hB₁,
    zero_mul,sub_zero,uncenteredProfileCoefficient]

theorem smooth_subset_uncentered_absolute_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → ∀ (S : Finset (Tuple J)) (K : ℝ),0<K →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let E := finiteHeckeEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (uncenteredProfileCoefficient R (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ B₁ B₂ s)) Φ K
      ‖E‖≤C*max 1 K*H^2 ∧ ‖E‖/H≤C*max 1 K*H := by
  obtain ⟨C,hC,hbound⟩ := smooth_subset_source_absolute_energy F Wslot W₁ W₂ Φ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ T B₁ B₂ s hP hX₁ hX₂ hB₁ hB₂ hX S K hK
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have he := hbound J hJ η m A t R ν hν P X₁ X₂
    (comparisonScale b₁) (T/comparisonScale b₁) T B₁ B₂ s
    hP hX₁ hX₂ (comparisonScale_pos b₁) (div_pos hT (comparisonScale_pos b₁))
    hB₁ hB₂ hX (comparison_product b₁ T) S K hK
  rw [profileCoefficient_eq_uncentered R (fun j : J => ν j.val)
    (fun j : J => Wslot j.val) (fun j : J => P j.val) W₁ W₂ a₁ b₁ ha₁ hs₁
    X₁ X₂ (T/comparisonScale b₁) B₁ B₂ s hB₁] at he
  exact he

theorem actual_small_width_uncentered_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → ∀ (S : Finset (Tuple J)) (Z mExp q M AExp ρ δ : ℝ),1≤Z →
      0≤mExp → 0≤q → mExp+q=M → M≤ρ → AExp≤M+δ →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      H=Z^AExp →
      ‖finiteHeckeEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (uncenteredProfileCoefficient R (fun j : J=>ν j.val)
          (fun j : J=>Wslot j.val) (fun j : J=>P j.val)
          W₁ W₂ X₁ X₂ B₁ B₂ s)) Φ (Z^mExp)‖/H≤C*Z^(M+ρ+δ) := by
  obtain ⟨C,hC,hbound⟩ := CenteredMomentTerminalEnergy.actual_small_width_source_energy
    F Wslot W₁ W₂ Φ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ T B₁ B₂ s
    hP hX₁ hX₂ hB₁ hB₂ hX S Z mExp q M AExp ρ δ hZ hm hq hM hsmall hA H hscale
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have he := hbound J hJ η m A t R ν hν P X₁ X₂
    (comparisonScale b₁) (T/comparisonScale b₁) T B₁ B₂ s
    hP hX₁ hX₂ (comparisonScale_pos b₁) (div_pos hT (comparisonScale_pos b₁))
    hB₁ hB₂ hX (comparison_product b₁ T) S Z mExp q M AExp ρ δ
    hZ hm hq hM hsmall hA hscale
  rw [profileCoefficient_eq_uncentered R (fun j : J => ν j.val)
    (fun j : J => Wslot j.val) (fun j : J => P j.val) W₁ W₂ a₁ b₁ ha₁ hs₁
    X₁ X₂ (T/comparisonScale b₁) B₁ B₂ s hB₁] at he
  exact he

end SevenEighths.CenteredMomentUncenteredTerminal

end

end OAI

end Source1004

/- Original source: OAI/NumberTheory/DirichletL/Moments/DetectorPlainSource.lean; sha256: 6d2028616da5965a0cfda227f940824920ad5b8e96ef62e9845096a1534f6b82 -/
section Source1005
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainSource
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentAddedZeroUniform
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleMask
open CenteredMomentUncenteredTerminal CenteredMomentHeckeExpansion
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentDivisorRowEnergy
open CenteredMomentRetainedEnergy CenteredMomentRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentSecondHeightFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def completePool (slots : ι→Finset (Ideal O)) (b₁ b₂ X₁ X₂ : ℝ) : Finset (Tuple ι) :=
  tuplePool slots (plainSupportPool b₁ X₁ (comparisonScale b₁))
    (plainSupportPool b₂ X₂ (X₁*X₂/comparisonScale b₁))

lemma support_zero (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) : W 0=0 := by
  by_contra hn
  have := (hs hn).1
  linarith

lemma comparison_row_zero (η : Character) (m A z : O) (t : ℝ)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) :
    rowTwistedSum η m A z W t (comparisonScale b)=0 := by
  rw [rowTwistedSum_eq_weight]
  calc
    _ = ∑' _I : Ideal O, (0:ℂ) := by
      apply tsum_congr
      intro I
      have h := comparison_first_zero W a b ha hs 1 I one_ne_zero
      simpa only [one_mul,mul_zero] using congrArg (fun v : ℂ=>rowWeight η m A z t I*v) h
    _ = 0 := tsum_zero

theorem complete_source_polynomial (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (R : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ X₁ X₂ : ℝ)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    (∑ I∈finiteColumns (completePool slots b₁ b₂ X₁ X₂),
      finiteColumnCoefficient (completePool slots b₁ b₂ X₁ X₂)
        (uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ 1 1 1) I *
          rowWeight η m A z t I)=
      (rowTwistedSum η (m*idealGenerator R) A z W₁ t X₁*
        rowTwistedSum η (m*idealGenerator R) A z W₂ t X₂)*
        ∏ i,rowSlot η (m*idealGenerator R) A z (slots i)
          (fun I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) t := by
  let : DecidableEq (ι⊕Fin 2) := Classical.decEq _
  have hs₁' : Function.support W₁⊆Set.Iic b₁ := fun x hx=>(hs₁ hx).2
  have hs₂' : Function.support W₂⊆Set.Iic b₂ := fun x hx=>(hs₂ hx).2
  have hy₁ := comparisonScale_pos b₁
  have hy₂ := div_pos (mul_pos hX₁ hX₂) hy₁
  have hc₁ := plainSupportPool_coverage W₁ b₁ X₁ (comparisonScale b₁)
    (support_zero W₁ a₁ b₁ ha₁ hs₁) hs₁' hX₁ hy₁
  have hc₂ := plainSupportPool_coverage W₂ b₂ X₂ (X₁*X₂/comparisonScale b₁)
    (support_zero W₂ a₂ b₂ ha₂ hs₂) hs₂' hX₂ hy₂
  have he := source_polynomial_eq_maskedRectangle η m A z t hmLam hm2 slots _ _ R 1
    ν Wslot P W₁ W₂ X₁ X₂ (comparisonScale b₁) (X₁*X₂/comparisonScale b₁) 1 1 hc₁ hc₂
  rw [profileCoefficient_eq_uncentered R ν Wslot P W₁ W₂ a₁ b₁ ha₁ hs₁
    X₁ X₂ (X₁*X₂/comparisonScale b₁) 1 1 1 one_ne_zero] at he
  simp only [map_one,Nat.cast_one,div_one] at he
  unfold completePool
  rw [he]
  have hr := actual_slot_rectangle_sum η (m*idealGenerator R) A z slots
    (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) t W₁ W₂ b₁ b₂
    X₁ X₂ (comparisonScale b₁) (X₁*X₂/comparisonScale b₁) hs₁' hs₂' hX₁ hX₂ hy₁ hy₂
  simp only [maskedRectangle,one_dvd,ite_true,one_mul]
  rw [hr,comparison_row_zero η (m*idealGenerator R) A z t W₁ a₁ b₁ ha₁ hs₁,
    zero_mul,sub_zero]

theorem positiveSlotRow_eq_complete_source (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (R : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ X₁ X₂ : ℝ)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    positiveSlotRow η (m*idealGenerator R) A z W₁ W₂ slots
      (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P t X₁ X₂=
      (Real.sqrt (X₁*X₂*∏ i,P i):ℂ)⁻¹*
      ∑ I∈finiteColumns (completePool slots b₁ b₂ X₁ X₂),
        finiteColumnCoefficient (completePool slots b₁ b₂ X₁ X₂)
          (uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ 1 1 1) I *
            rowWeight η m A z t I := by
  rw [complete_source_polynomial η m A z t hmLam hm2 slots R ν Wslot P W₁ W₂
    a₁ b₁ a₂ b₂ X₁ X₂ ha₁ ha₂ hs₁ hs₂ hX₁ hX₂]
  rfl

theorem positive_energy_eq_complete_source (η : Character) (t : ℝ) (keep : O→Prop)
    (slots : ι→Finset (Ideal O)) (R : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (hP : ∀ i,0<P i)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ X₁ X₂ : ℝ)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑' z : O,if keep z then
      ‖positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ slots
        (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P t X₁ X₂‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)=
      sourceRestrictedEnergy keep (finiteColumns (completePool slots b₁ b₂ X₁ X₂))
        (finiteColumnCoefficient (completePool slots b₁ b₂ X₁ X₂)
          (uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ 1 1 1))
        (heightCoeff η t) Φ K / (X₁*X₂*∏ i,P i) := by
  have htotal : 0<X₁*X₂*∏ i,P i := mul_pos (mul_pos hX₁ hX₂)
    (Finset.prod_pos (fun i _=>hP i))
  unfold sourceRestrictedEnergy restrictedEnergy
  rw [← tsum_div_const]
  apply tsum_congr
  intro z
  rw [height_source_row]
  by_cases hk : keep z
  · rw [ite_eq_left hk,ite_eq_left hk,
      positiveSlotRow_eq_complete_source η fixedBadMask 1 z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) slots R ν Wslot P W₁ W₂
        a₁ b₁ a₂ b₂ X₁ X₂ ha₁ ha₂ hs₁ hs₂ hX₁ hX₂,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _ htotal]
    ring
  · simp only [ite_eq_right hk,zero_div]

end SevenEighths.CenteredMomentDetectorPlainSource

end

end OAI

end Source1005

/- Original source: OAI/NumberTheory/DirichletL/Energy/OriginalSource.lean; sha256: b6f22f83c25e667d0c93ff0c927dc17eb78363a5eae7950da501f0a711e26f5c -/
section Source1006
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyOriginalSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleMask
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentHeckeHeight
open CenteredMomentDivisorRowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRectangleEnergy
open CenteredMomentPositiveSummability CenteredMomentPlainEnergy CenteredMomentRowNorm
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance energyOriginalSourceDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def completeInput (s : Data ι) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hν : ∀i I,‖s.ν i I‖≤1) (hW : ∀i x,‖s.W i x‖≤s.M i)
    (lo hi : ℝ) (hlo : 0<lo) (hl : ∀i,lo≤s.lo i) (hh : ∀i,s.hi i≤hi) : Input ι where
  toData := s
  plain₁ := plainSupportPool s.b₁ s.X₁ s.Y₁
  plain₂ := plainSupportPool s.b₂ s.X₂ s.Y₂
  plain₁_ne := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI|hI
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
  plain₂_ne := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI|hI
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
  coverage₁ := plainSupportPool_coverage s.W₁ s.b₁ s.X₁ s.Y₁ hz₁ s.support₁ s.X₁_pos s.Y₁_pos
  coverage₂ := plainSupportPool_coverage s.W₂ s.b₂ s.X₂ s.Y₂ hz₂ s.support₂ s.X₂_pos s.Y₂_pos
  ν_bound := hν
  W_bound := hW
  lower := lo
  upper := hi
  lower_pos := hlo
  lower_le := hl
  upper_ge := hh

omit [DecidableEq ι] in
lemma input_tuplePool (s : Input ι) :
    Fintype.piFinset s.pools=tuplePool s.slots s.plain₁ s.plain₂ := by
  ext v
  simp only [Fintype.mem_piFinset,tuplePool,tuplePools,Input.pools]

lemma input_polynomial_difference (s : Input ι) (R : Ideal O) (z : O) :
    (∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
      rowWeight s.η fixedBadMask 1 z s.t I)=
    (rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t s.X₁*
      rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₂ s.t s.X₂-
     rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t s.Y₁*
      rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₂ s.t s.Y₂)*
        ∏i,rowSlot s.η (fixedBadMask*idealGenerator R) 1 z (s.slots i)
          (s.toData.coefficient i) s.t := by
  unfold coefficient
  rw [input_tuplePool]
  rw [source_polynomial_eq_maskedRectangle s.η fixedBadMask 1 z s.t
    (dvd_mul_right _ _) (dvd_mul_left _ _) s.slots s.plain₁ s.plain₂ R 1
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 s.coverage₁ s.coverage₂]
  simp only [map_one,Nat.cast_one,div_one,maskedRectangle,one_dvd,ite_true,one_mul]
  exact actual_slot_rectangle_sum s.η (fixedBadMask*idealGenerator R) 1 z s.slots
    s.toData.coefficient s.t s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂
    s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos

lemma normalized_input_difference (s : Input ι) (R : Ideal O) (z : O) :
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.X₁ s.X₂-
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.Y₁ s.Y₂=
    (Real.sqrt (CenteredMomentAmplificationChildInput.volume s):ℂ)⁻¹*
      ∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
        rowWeight s.η fixedBadMask 1 z s.t I := by
  rw [input_polynomial_difference]
  unfold positiveSlotRow CenteredMomentAmplificationChildInput.volume
  rw [s.same_product]
  ring

omit [DecidableEq ι] in
lemma input_energy_hasSum (s : Input ι) (R : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O=>
      ‖∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
        rowWeight s.η fixedBadMask 1 z s.t I‖^2*
          (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
      (finiteHeckeEnergy s.η fixedBadMask 1 s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R 1) Φ K).re := by
  have hs := Complex.hasSum_re (rowEnergy_summable Finset.univ
    (sourceGenerator (finiteColumns (Fintype.piFinset s.pools))) (sourceGenerator_supported _)
    (fun I=>coefficient s R 1 I*rowWeight s.η fixedBadMask 1 1 s.t I) Φ K hK).hasSum
  change HasSum _ (rowEnergy _ _ _ Φ K).re at hs
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  simpa only [finiteHeckeEnergy_eq s.η fixedBadMask 1 s.t (dvd_mul_right _ _) (dvd_mul_left _ _),
    finite_hecke_sum_eq_rowPolynomial s.η fixedBadMask 1 _ s.t (dvd_mul_right _ _) (dvd_mul_left _ _)] using hs

theorem kept_difference_energy (s : Input ι) (R : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑'z : O,if keep z then
      ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
          s.toData.coefficient s.P s.t s.X₁ s.X₂-
        positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
          s.toData.coefficient s.P s.t s.Y₁ s.Y₂‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)=
      CenteredMomentRestrictedSource.sourceRestrictedEnergy keep
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1)
        (CenteredMomentHeckeColumnWindow.heightCoeff s.η s.t) Φ K /
          CenteredMomentAmplificationChildInput.volume s := by
  unfold CenteredMomentRestrictedSource.sourceRestrictedEnergy
    CenteredMomentRestrictedEnergy.restrictedEnergy
  rw [←tsum_div_const]
  apply tsum_congr
  intro z
  rw [height_source_row]
  by_cases hk : keep z
  · rw [ite_eq_left hk,ite_eq_left hk,normalized_input_difference,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _
        (CenteredMomentAmplificationChildInput.volume_pos s)]
    ring
  · simp only [ite_eq_right hk,zero_div]

omit [DecidableEq ι] in
lemma input_positive_summable (s : Input ι) (R : Ideal O) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K X₁ X₂ : ℝ) (hK : 0<K) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    Summable (fun z : O=>if keep z then
      ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t X₁ X₂‖^2*
          (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B,hB⟩ := product_bounded s.η (fixedBadMask*idealGenerator R) 1 s.t
    (Real.sqrt (X₁*X₂*∏i,s.P i):ℂ)⁻¹ s.W₁ s.W₂ s.b₁ s.b₂ X₁ X₂
    s.support₁ s.support₂ hX₁ hX₂ s.slots s.toData.coefficient
  exact bounded_radial_summable _ B hB keep Φ K hK

theorem positive_energy_comparison (s : Input ι) (R : Ideal O)
    (r : CenteredMomentRadialEligibleEnergy.Radial) :
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
      s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
    2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R 1) r.profile r.scale‖ / CenteredMomentAmplificationChildInput.volume s+
    2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
      s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale := by
  let V := CenteredMomentAmplificationChildInput.volume s
  have hV : 0<V := CenteredMomentAmplificationChildInput.volume_pos s
  let f : O→ℝ := fun z=>
    (‖∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
      rowWeight s.η fixedBadMask 1 z s.t I‖^2*
      (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re)/V
  let g : O→ℝ := fun z=>if r.keep z then
    ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.Y₁ s.Y₂‖^2*
      (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0
  have hf := (input_energy_hasSum s R r.profile r.scale r.scale_pos).div_const V
  have hg := input_positive_summable s R r.keep r.profile r.scale s.Y₁ s.Y₂
    r.scale_pos s.Y₁_pos s.Y₂_pos
  have hfn (z : O) : 0≤f z := div_nonneg (mul_nonneg (sq_nonneg _) (r.nonneg z)) hV.le
  have hgn (z : O) : 0≤g z := by
    dsimp only [g]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (r.nonneg z)
    · rfl
  unfold CenteredMomentInductionEnergy.energy
  apply Real.tsum_le_of_sum_le (fun z=>by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (r.nonneg z)
    · rfl)
  intro rows
  have hp (z : O) :
      (if r.keep z then
        ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
          s.toData.coefficient s.P s.t s.X₁ s.X₂‖^2*
          (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0) ≤ 2*f z+2*g z := by
    by_cases hk : r.keep z
    · let x := positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t s.X₁ s.X₂
      let y := positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t s.Y₁ s.Y₂
      have hn : ‖x‖≤‖x-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (x-y) y
      have hsq : ‖x‖^2≤2*‖x-y‖^2+2*‖y‖^2 := by
        have hh := pow_le_pow_left₀ (norm_nonneg x) hn 2
        nlinarith [sq_nonneg (‖x-y‖-‖y‖)]
      dsimp only [x,y] at hsq
      rw [normalized_input_difference,CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hV] at hsq
      have hh := mul_le_mul_of_nonneg_right hsq (r.nonneg z)
      dsimp only [f,g]
      rw [ite_eq_left hk,ite_eq_left hk]
      convert hh using 1 ; ring
    · rw [ite_eq_right hk]
      exact add_nonneg (mul_nonneg (by norm_num) (hfn z)) (mul_nonneg (by norm_num) (hgn z))
  have hb := Finset.sum_le_sum (fun z (_:z∈rows)=>hp z)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum] at hb
  have hs := sum_le_hasSum rows (fun z _=>hfn z) hf
  have ht := sum_le_hasSum rows (fun z _=>hgn z) hg.hasSum
  have he := div_le_div_of_nonneg_right
    (Complex.re_le_norm (finiteHeckeEnergy s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.profile r.scale)) hV.le
  change ∑z∈rows,f z≤_ at hs
  change ∑z∈rows,g z≤∑'z,g z at ht
  change _≤2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.profile r.scale‖/V+2*∑'z,g z
  rw [mul_div_assoc]
  linarith

section Natural
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
variable {Z Bmask bΦ a b : ℝ}
variable (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0<a)
variable (S : ι→Finset (Ideal O)) (hp : ∀i,∀I∈S i,Prime I)
variable (ν : ι→Character) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
variable (hP : ∀i,0<P i) (hM : ∀i,1≤M i)
variable (aslot bslot : ℝ) (haslot : 0<aslot)
variable (hsSlot : ∀i,Function.support (Wslot i)⊆Set.Icc aslot bslot)
variable (hWslot : ∀i x,‖Wslot i x‖≤M i)
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hsame : Y₁*Y₂=X₁*X₂)

def naturalData : Data ι where
  η := state.character
  m := state.mask
  A := 1
  t := t
  slots := S
  prime := hp
  ν := fun i=>idealCoeff (ν i)
  W := Wslot
  lo := fun _=>aslot
  hi := fun _=>bslot
  P := P
  lo_pos := fun _=>haslot
  P_pos := hP
  support := hsSlot
  W₁ := p.profile 0
  W₂ := p.profile 1
  X₁ := X₁
  X₂ := X₂
  Y₁ := Y₁
  Y₂ := Y₂
  M := M
  M_ge_one := hM
  coefficient_bound := fun i I _=>by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one (ν i) I) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hWslot i ((Ideal.absNorm I:ℝ)/P i))
  b₁ := b
  b₂ := b
  support₁ := fun x hx=>(p.support 0 hx).2
  support₂ := fun x hx=>(p.support 1 hx).2
  X₁_pos := hX₁
  X₂_pos := hX₂
  Y₁_pos := hY₁
  Y₂_pos := hY₂
  same_product := hsame
  rows := ∅
  weight := fun _=>0
  weight_nonneg := fun _ _=>le_refl _

def naturalInput : Input ι :=
  completeInput (naturalData state p S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame)
    (CenteredMomentDetectorPlainSource.support_zero (p.profile 0) a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero (p.profile 1) a b ha (p.support 1))
    (fun i I=>idealCoeff_norm_le_one (ν i) I) hWslot aslot bslot haslot
    (fun _=>le_refl _) (fun _=>le_refl _)

theorem natural_energy_comparison :
    let inp := naturalInput state p ha S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame
    CenteredMomentInductionEnergy.energy state.character state.mask 1 t
      (p.profile 0) (p.profile 1) S
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P X₁ X₂
      state.radial.keep state.radial.profile state.radial.scale ≤
    2*‖finiteHeckeEnergy state.character fixedBadMask 1 t
      (finiteColumns (Fintype.piFinset inp.pools)) (coefficient inp state.puncture 1)
      state.radial.profile state.radial.scale‖/(X₁*X₂*∏i,P i)+
    2*CenteredMomentInductionEnergy.energy state.character state.mask 1 t
      (p.profile 0) (p.profile 1) S
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P Y₁ Y₂
      state.radial.keep state.radial.profile state.radial.scale :=
  positive_energy_comparison
    (naturalInput state p ha S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame) state.puncture state.radial

end Natural
end SevenEighths.CenteredMomentEnergyOriginalSource

end

end OAI

end Source1006

/- Original source: OAI/NumberTheory/DirichletL/Energy/Floor.lean; sha256: ca646aeb42c50b87f24485bf6aede2b8044d51a0f3970a72d5677e7b0625f7d0 -/
section Source1007
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyState
open HeckeFamily CenteredMomentNaturalMaskedFloor
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound

theorem exists_zero_floor (a b bΦ Bmask ε:ℝ)(ha:0<a)(hb:0≤b)
    (hbΦ:0<bΦ)(hmask:0≤Bmask)(hε:0<ε):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀Q:Ideal HeckeFamily.O,ZeroBound Q a b bΦ Bmask (ε/16) ε degree S C 1:=by
  let e:ℝ:=ε/(4*(Bmask+1))
  have he:0<e:=div_pos hε (by positivity)
  have hbudget:e*Bmask+4*(ε/16)≤ε:=by
    have hcost:e*Bmask≤ε/4:=by
      have hinc:Bmask≤Bmask+1:=by linarith
      have hh:=mul_le_mul_of_nonneg_left hinc he.le
      have hid:e*(Bmask+1)=ε/4:=by dsimp [e];field_simp
      rw [hid] at hh
      exact hh
    linarith
  obtain ⟨degree,S,C,hC,hfloor⟩:=natural_masked_floor a b e ha hb he
  refine ⟨degree,S,C*bΦ^4,mul_pos hC (pow_pos hbΦ _),?_⟩
  intro Q Z hZ₀ s hQ hs p t X₁ X₂ hX₁ hX₂
  have hZ:=s.base_ge_one
  have hZ0:0<Z:=zero_lt_one.trans_le hZ
  have hrad: (s.puncture.radical.absNorm:ℝ)^e≤Z^(Bmask*e):=by
    rw [Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow (by positivity) s.radical_bound he.le
  have hp:Z^(Bmask*e)*Z^(s.width+4*(ε/16))≤Z^(s.width+ε):=by
    rw [←Real.rpow_add hZ0]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    linarith
  have hh:=hfloor (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
    s.character s.fixedModulus s.puncture s.radial bΦ s.puncture_ne_zero hbΦ.le
    s.radial_support s.row_ne_zero s.nonexceptional Z s.rowWidth s.characterWidth
    (ε/16) t X₁ X₂ hZ s.row_nonneg s.character_nonneg s.scale_eq hs hX₁ hX₂ s.modulus_bound
  rw [s.plainEnergy_eq_zero]
  change CenteredMomentCoreFloor.zeroEnergy _ _ _ _ _ _ _ _ _≤_
  apply hh.trans
  have hd:=diagonalControl_nonneg s.radial.profile
  have hc:=p.control_nonneg S
  change C*(s.puncture.radical.absNorm:ℝ)^e*bΦ^4*diagonalControl s.radial.profile*
    (p.control S)^2*(1+‖t‖)^degree*Z^(s.width+4*(ε/16))≤_
  calc
    _≤C*Z^(Bmask*e)*bΦ^4*diagonalControl s.radial.profile*
      (p.control S)^2*(1+‖t‖)^degree*Z^(s.width+4*(ε/16)):=by gcongr
    _=(C*bΦ^4*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree)*
      (Z^(Bmask*e)*Z^(s.width+4*(ε/16))):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentEnergyState

end

end OAI

end Source1007

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeNonprincipal.lean; sha256: b831d55708c640f42f4bdb5f78cf0074af4fc134cb974e3b94a6b8b6ee1e11d9 -/
section Source1008
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckePrimeNonprincipal
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem inverse_twist_elementCoeff (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n) (n : O) :
    elementCoeff ((χ.inverse.product θ).inverse) n =
      rowTwist (elementHom (η.product θ.inverse)) m f z n := by
  rw [elementCoeff_inverse,elementCoeff_product,elementCoeff_inverse,mul_inv_rev,inv_inv,hχ]
  change _ = elementCoeff (η.product θ.inverse) n * idealRowHom (m^6*f^4*z) (Ideal.span {n})
  rw [elementCoeff_product,elementCoeff_inverse]
  change (elementCoeff θ n)⁻¹ *
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) = _
  ring

theorem twisted_nonprincipal (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : f^4*z=(u : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime (((η.product θ.inverse).modulus*Ideal.span {m}*Ideal.span {(72 : O)})*J) (P^c)) :
    (χ.inverse.product θ).residue≠1 := by
  have hn := HeckeRowNonprincipal.actual_row_nonprincipal (η.product θ.inverse)
    ((χ.inverse.product θ).inverse) m f z hmLam hm2 u a b r hr hpr hx P J hg hchar hJ
    hc hc6 hsplit hcop (inverse_twist_elementCoeff η χ θ m f z hχ)
  intro h
  apply hn
  change (χ.inverse.product θ).residue⁻¹=1
  rw [h,inv_one]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem fixed_twist_modulus (θ : RayQuotient.Characters M H) :
    ((HeckeRayFamily.character M 1).product
      (HeckeRayQuotient.character M H hH θ).inverse).modulus=M := by
  change M⊓M=M
  simp

theorem fixed_ray_twisted_nonprincipal (χ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom (HeckeRayFamily.character M 1)) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : f^4*z=(u : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime ((M*Ideal.span {m}*Ideal.span {(72 : O)})*J) (P^c))
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ.inverse θ).residue≠1 := by
  apply twisted_nonprincipal (HeckeRayFamily.character M 1) χ
    (HeckeRayQuotient.character M H hH θ) m f z hχ hmLam hm2 u a b r hr hpr hx
    P J hg hchar hJ hc hc6 hsplit
  rwa [fixed_twist_modulus M H hH θ]

end SevenEighths.HeckePrimeNonprincipal

end

end OAI

end Source1008

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorFamilyInclusion.lean; sha256: 9a0844dc067d7a136c751af204d5ef48c64b0d0ebc5384ad718bb572e734a2f3 -/
section Source1009
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.HeckeDetectorFamilyInclusion
open HeckeFamily HeckeDetectorZeros Complex

theorem maximum_le_of_inclusion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ)
    (hinclude : ∀ i,∃ j, ∀ s : ℂ, LFunction (χ i) s=LFunction (ψ j) s) :
    zeroMaximum χ hχ T≤zeroMaximum ψ hψ T := by
  rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
  · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained χ hχ T hm
    obtain ⟨j,hj⟩ := hinclude i
    rw [←hs]
    apply zero_re_le_maximum ψ hψ T j
    · rw [hs]
      exact hm.le
    · exact ht
    · rw [←hj s]
      exact hz
  · exact hm.trans (zeroMaximum_bounds ψ hψ T).1

theorem maximum_sum_left {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ) :
    zeroMaximum χ hχ T≤zeroMaximum (Sum.elim χ ψ) (Sum.rec hχ hψ) T := by
  apply maximum_le_of_inclusion
  intro i
  exact ⟨Sum.inl i,fun _ => rfl⟩

theorem maximum_sum_right {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ) :
    zeroMaximum ψ hψ T≤zeroMaximum (Sum.elim χ ψ) (Sum.rec hχ hψ) T := by
  apply maximum_le_of_inclusion
  intro i
  exact ⟨Sum.inr i,fun _ => rfl⟩

theorem inverse_nonprincipal (χ : Character) (hχ : χ.residue≠1) : χ.inverse.residue≠1 := by
  change χ.residue⁻¹≠1
  simpa only [ne_eq,inv_eq_one] using hχ

theorem maximum_inverse {ι : Type*} [Fintype ι] (χ : ι→Character)
    (hχ : ∀ i,(χ i).residue≠1) (T : ℝ) :
    zeroMaximum (fun i => (χ i).inverse) (fun i => inverse_nonprincipal (χ i) (hχ i)) T=
      zeroMaximum χ hχ T := by
  let ψ := fun i => (χ i).inverse
  have hψ := fun i => inverse_nonprincipal (χ i) (hχ i)
  apply le_antisymm
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum ψ hψ T) with hm | hm
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained ψ hψ T hm
      rw [LFunction_inverse_conj (χ i) (hχ i),map_eq_zero] at hz
      have hh := zero_re_le_maximum χ hχ T i (s:=conj s)
        (by simpa only [conj_re,hs] using hm.le) (by simpa using ht) hz
      simpa only [conj_re,hs] using hh
    · exact hm.trans (zeroMaximum_bounds χ hχ T).1
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained χ hχ T hm
      have hz' : LFunction (ψ i) (conj s)=0 := by
        rw [LFunction_inverse_conj (χ i) (hχ i),conj_conj,hz,map_zero]
      have hh := zero_re_le_maximum ψ hψ T i (s:=conj s)
        (by simpa only [conj_re,hs] using hm.le) (by simpa using ht) hz'
      simpa only [conj_re,hs] using hh
    · exact hm.trans (zeroMaximum_bounds ψ hψ T).1

end SevenEighths.HeckeDetectorFamilyInclusion

end

end OAI

end Source1009

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorPrimeFamily.lean; sha256: c0b3ade88e0c84f1739e4ee55ed9cc45cfc22fc5a16c18b93d3def57693782ec -/
section Source1010
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate BigOperators
namespace SevenEighths.HeckeDetectorPrimeFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

structure RowData (M : Ideal O) where
  m : O
  u : O
  m_ne_zero : m≠0
  u_ne_zero : u≠0
  lambda_dvd : λ₀∣m
  two_dvd : (2 : O)∣m
  modulus_le : M≤Ideal.span {m}

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def RowData.base (data : RowData M) : Character :=
  Classical.choose (exists_row_character_with_conductor (HeckeRayFamily.character M 1)
    data.m 1 data.u data.m_ne_zero one_ne_zero data.u_ne_zero data.lambda_dvd data.two_dvd)

theorem RowData.base_spec (data : RowData M) (n : O) :
    elementCoeff (data.base M) n=
      rowTwist (elementHom (HeckeRayFamily.character M 1)) data.m 1 data.u n :=
  (Classical.choose_spec (exists_row_character_with_conductor (HeckeRayFamily.character M 1)
    data.m 1 data.u data.m_ne_zero one_ne_zero data.u_ne_zero data.lambda_dvd data.two_dvd)).2 n

theorem RowData.base_conductor (data : RowData M) :
    (data.base M).modulus.absNorm≤rowConductorBound (HeckeRayFamily.character M 1) data.m 1 data.u :=
  (Classical.choose_spec (exists_row_character_with_conductor (HeckeRayFamily.character M 1)
    data.m 1 data.u data.m_ne_zero one_ne_zero data.u_ne_zero data.lambda_dvd data.two_dvd)).1

def RowData.character (data : RowData M) : Character := (data.base M).inverse

variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH in
theorem RowData.coefficient_on_ray (data : RowData M) (P : Ideal O) [P.IsMaximal]
    (hg : λ₀∉P) (hP : P∈RayQuotient.identityClass M H) :
    idealCoeff (data.character M) P=starRingEnd ℂ (idealRowHom data.u P) := by
  have hc := HeckePrimeRow.identityClass_coprime_larger M H hP data.modulus_le
  rw [RowData.character,idealCoeff_inverse_conj,
    idealCoeff_eq_row _ (data.base M) data.m 1 data.u (data.base_spec M),
    HeckePrimeRow.identityClass_principal_coeff M H hH hP,one_mul,one_pow,mul_one,
    idealRowHom_argument_mul,idealRowHom_prime_sixth_mask data.m P hg,ite_eq_left hc,one_mul]

include hH in
theorem RowData.amplitude_eq (data : RowData M) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H data.u W b D z=
      HeckePrimeRay.rayPrimePolynomial M H (data.character M) W b D (1-z.re) z.im := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude HeckePrimeRay.rayPrimePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨_,hprime,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hg := HeckePrimeRow.identityClass_prime_good M H data.m data.lambda_dvd data.modulus_le P hclass
  rw [data.coefficient_on_ray M H hH P hg hclass]
  have he : -HeckeDyadic.shift (1-z.re) z.im=z-1 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  simp only [HeckePrimeAnnular.annularWeight,he]
  ring

theorem RowData.twisted_conductor (data : RowData M) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm≤
      M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
        (Ideal.span {data.u}).absNorm := by
  apply HeckePrimeScale.twisted_row_modulus_bound M H hH (data.character M) data.m data.u
  exact data.base_conductor M

theorem RowData.twisted_nonprincipal (data : RowData M)
    (unit : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : data.u=(unit : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime ((M*Ideal.span {data.m}*Ideal.span {(72 : O)})*J) (P^c))
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (data.character M) θ).residue≠1 := by
  exact HeckePrimeNonprincipal.fixed_ray_twisted_nonprincipal M H hH (data.base M)
    data.m 1 data.u (data.base_spec M) data.lambda_dvd data.two_dvd unit a b r hr hpr
    (by simpa using hx) P J hg hchar hJ hc hc6 hsplit hcop θ

structure Ramification (data : RowData M) where
  unit : Oˣ
  lambda_power : ℕ
  two_power : ℕ
  remaining : O
  supported : CanonicalQuadraticSieve.Supported (Ideal.span {remaining})
  primary : λ₀^2∣remaining-1
  decomposition : data.u=(unit : O)*λ₀^lambda_power*(2 : O)^two_power*remaining
  prime : Ideal O
  rest : Ideal O
  maximal : prime.IsMaximal
  prime_good : λ₀∉prime
  odd : ringChar (O ⧸ prime)≠2
  rest_supported : CanonicalQuadraticSieve.Supported rest
  multiplicity : ℕ
  multiplicity_pos : 1≤multiplicity
  not_sixfold : ¬6∣multiplicity
  split : Ideal.span {remaining}=prime^multiplicity*rest
  coprime : IsCoprime ((M*Ideal.span {data.m}*Ideal.span {(72 : O)})*rest) (prime^multiplicity)

theorem Ramification.nonprincipal {data : RowData M} (cert : Ramification M data)
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (data.character M) θ).residue≠1 := by
  let := cert.maximal
  exact data.twisted_nonprincipal M H hH cert.unit cert.lambda_power cert.two_power
    cert.remaining cert.supported cert.primary cert.decomposition cert.prime cert.rest cert.prime_good
    cert.odd cert.rest_supported cert.multiplicity_pos cert.not_sixfold cert.split cert.coprime θ

end SevenEighths.HeckeDetectorPrimeFamily

end

end OAI

end Source1010

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorRelativePrime.lean; sha256: f3ec824537fd87cd3ccabb4a4c5c67c300c02ee8058d196415fb34d491beb814 -/
section Source1011
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRelativePrime
open HeckeFamily HeckeDetectorPrimeFamily

theorem idealCoeff_ne_zero_of_coprime (ν : Character) (J : Ideal O)
    (hJ : J≠0) (hc : IsCoprime J ν.modulus) : idealCoeff ν J≠0 := by
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν hg]
  apply MulChar.apply_ne_zero_iff.mpr
  apply (IdealCharacter.isUnit_mk_iff_isCoprime ν.modulus _).mpr
  simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hc

theorem idealCoeff_inverse (ν : Character) (J : Ideal O) :
    idealCoeff ν.inverse J=(idealCoeff ν J)⁻¹ := by
  by_cases hJ : J=0
  · subst J
    simp only [map_zero,inv_zero]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν.inverse hg,
    idealCoeff_span ν hg,HeckeFamily.elementCoeff_inverse]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem relative_coefficient_on_ray (ν χ : Character) (hM : M≤ν.modulus)
    (J : Ideal O) (hJ : J∈RayQuotient.identityClass M H) :
    idealCoeff ((ν.product χ).product ν.inverse) J=idealCoeff χ J := by
  have hn := idealCoeff_ne_zero_of_coprime ν J hJ.1
    (HeckePrimeRow.identityClass_coprime_larger M H hJ hM)
  rw [idealCoeff_product,idealCoeff_product,idealCoeff_inverse]
  field_simp

theorem physical_eq_relative_average (data : RowData M) (ν : Character)
    (hM : M≤ν.modulus) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H data.u W b D z=
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H,
          HeckePrimeAnnular.primePolynomial
            ((ν.product (data.character M)).product
              (ν.inverse.product (HeckeRayQuotient.character M H hH θ)))
            W b D (1-z.re) z.im := by
  rw [data.amplitude_eq M H hH]
  have he : HeckePrimeRay.rayPrimePolynomial M H (data.character M) W b D (1-z.re) z.im=
      HeckePrimeRay.rayPrimePolynomial M H ((ν.product (data.character M)).product ν.inverse)
        W b D (1-z.re) z.im := by
    unfold HeckePrimeRay.rayPrimePolynomial
    congr 1
    apply Finset.sum_congr rfl
    intro J hJ
    rw [relative_coefficient_on_ray M H ν (data.character M) hM J (Finset.mem_filter.mp hJ).2.2]
  rw [he,HeckePrimeRay.rayPrimePolynomial_eq_average M H hH]
  congr 1
  apply Finset.sum_congr rfl
  intro θ hθ
  unfold HeckePrimeAnnular.primePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [HeckePrimeRay.twistedFamily,idealCoeff_product]
  ring

end SevenEighths.HeckeDetectorRelativePrime

end

end OAI

end Source1011

/- Original source: OAI/NumberTheory/DirichletL/Moments/DetectorDictionarySlots.lean; sha256: d263889b617997352d8480a25fabccb3f5e8af814399deda52d563375eee6541 -/
section Source1012
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure CanonicalRowCompletion
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open HeckeDetectorRelativePrime
local notation "O" => HeckeFamily.O

def physicalSlotCoefficient (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ) (P : Ideal O) : ℂ :=
  idealCoeff η.inverse P*conj (W ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(z-1))

lemma physicalSlotCoefficient_norm (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ) (P : Ideal O) :
    ‖physicalSlotCoefficient η W D z P‖≤‖W ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(z-1)‖ := by
  rw [physicalSlotCoefficient,norm_mul,RCLike.norm_conj]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η.inverse P)

lemma physicalSlotCoefficient_annular (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ)
    (P : Ideal O) (hP : P≠0) (hD : 0<D) :
    physicalSlotCoefficient η W D z P=idealCoeff η.inverse P*
      HeckePrimeAnnular.annularWeight (fun y=>conj (W y)) D (1-z.re) (-z.im) P := by
  have hn : 0<(P.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  unfold physicalSlotCoefficient HeckePrimeAnnular.annularWeight
  rw [map_mul,HeckeInverseAmplification.conj_positive_cpow _ (div_pos hn hD)]
  have he : conj (z-1)= -HeckeDyadic.shift (1-z.re) (-z.im) := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  rw [he]

theorem physical_slot_conj (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η : Character) (m u : O) (hmLam : ConcretePrimeRowBridge.goodLambda∣m)
    (hMm : M≤Ideal.span {m}) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) (hD : 0<D)
    (hη : ∀P∈primePool M H b D,W ((P.absNorm:ℝ)/D)≠0→IsCoprime P η.modulus) :
    normalizedSlot η m 1 u (primePool M H b D) (physicalSlotCoefficient η W D z) 0 D=
      conj (HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z) := by
  unfold normalizedSlot rowSlot HeckePrimeRow.canonicalPrimeAmplitude
  rw [←sqrt_inverse_cpow D hD,map_mul]
  simp only [map_inv₀,Complex.conj_ofReal,Complex.ofReal_zero,one_mul,mul_zero,Complex.cpow_zero,mul_one,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  have hP' : P∈primePool M H b D := hP
  obtain ⟨_,hp,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := HeckePrimeRow.identityClass_prime_good M H m hmLam hMm P hclass
  have hcop := HeckePrimeRow.identityClass_coprime_larger M H hclass hMm
  rw [idealRowHom_argument_mul,idealRowHom_prime_sixth_mask m P hg,ite_eq_left hcop,one_mul]
  by_cases hw : W ((P.absNorm:ℝ)/D)=0
  · simp only [physicalSlotCoefficient,hw,zero_mul,map_zero,mul_zero,zero_mul]
  · have hn := idealCoeff_ne_zero_of_coprime η P hp.ne_zero (hη P hP' hw)
    simp only [physicalSlotCoefficient,HeckeDetectorRelativePrime.idealCoeff_inverse,map_mul,starRingEnd_self_apply]
    field_simp

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end Source1012

/- Original source: OAI/NumberTheory/DirichletL/Moments/DetectorDictionaryRelativeSlots.lean; sha256: 19d58851315cccffed32a31a8609101e3cf162381c2c0cf2b7122e93ca5040cb -/
section Source1013
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma normalizedSlot_character (η ν : Character) (m A z : O)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (t D : ℝ) :
    normalizedSlot η m A z S (fun P=>idealCoeff ν P*β P) t D=
      normalizedSlot (η.product ν) m A z S β t D := by
  unfold normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  rw [idealCoeff_product]
  ring

lemma product_row_presentation (η χ ν : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n) :
    ∀n,elementCoeff (χ.product ν) n=rowTwist (elementHom (η.product ν)) m 1 (A*z) n := by
  intro n
  rw [elementCoeff_product,hrow]
  change (elementCoeff η n*((idealRowHom (m^6*1^4*(A*z))).toMonoidHom.comp principalIdealHom.toMonoidHom) n)*elementCoeff ν n=
    elementCoeff (η.product ν) n*((idealRowHom (m^6*1^4*(A*z))).toMonoidHom.comp principalIdealHom.toMonoidHom) n
  rw [elementCoeff_product]
  ring

theorem relative_normalizedSlot_eq_ray (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ ν : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (W : ℝ→ℂ) (b D σ t v : ℝ) (hD : 0<D) :
    normalizedSlot η m A z (primePool M H b D)
      (fun P=>idealCoeff ν P*HeckePrimeAnnular.annularWeight W D σ v P) t D=
      (D:ℂ)^(Complex.I*t)*HeckePrimeRay.rayPrimePolynomial M H (χ.product ν) W b D σ (t+v) := by
  rw [normalizedSlot_character]
  exact CenteredMomentPrimeSlotShift.normalizedSlot_eq_ray M H (η.product ν) (χ.product ν)
    m A z (product_row_presentation η χ ν m A z hrow) W b D σ t v hD

theorem physicalSlot_eq_relativeRay (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ : Character) (m A u : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*u) n)
    (W : ℝ→ℂ) (b D t : ℝ) (z : ℂ) (hD : 0<D) :
    normalizedSlot η m A u (primePool M H b D) (physicalSlotCoefficient η W D z) t D=
      (D:ℂ)^(Complex.I*t)*HeckePrimeRay.rayPrimePolynomial M H (χ.product η.inverse)
        (fun y=>conj (W y)) b D (1-z.re) (t-z.im) := by
  have he : normalizedSlot η m A u (primePool M H b D) (physicalSlotCoefficient η W D z) t D=
      normalizedSlot η m A u (primePool M H b D)
        (fun P=>idealCoeff η.inverse P*HeckePrimeAnnular.annularWeight (fun y=>conj (W y)) D (1-z.re) (-z.im) P) t D := by
    unfold normalizedSlot rowSlot
    congr 1
    apply Finset.sum_congr rfl
    intro P hP
    rw [physicalSlotCoefficient_annular η W D z P (Finset.mem_filter.mp hP).2.1.ne_zero hD]
  rw [he]
  exact relative_normalizedSlot_eq_ray M H η χ η.inverse m A u hrow
    (fun y=>conj (W y)) b D (1-z.re) t (-z.im) hD

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end Source1013

/- Original source: OAI/NumberTheory/DirichletL/Moments/FixedRayInducingTransport.lean; sha256: 7c10dd322c78666e825c349f0e820ac1a14bb2d64caf7ce9c4a1615cbda9f0c1 -/
section Source1014
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFixedRayInducingTransport
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile
open CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentExceptionalPair CenteredMomentFixedRowMask
local notation "O" => HeckeFamily.O

theorem modulus_generator_ne_zero (ν : Character) :
    idealGenerator ν.modulus ≠ 0 :=
  idealGenerator_ne_zero ν.modulus ν.modulus_ne_bot

theorem modulus_unit_iff (ν : Character) (n : O) :
    IsUnit (Ideal.Quotient.mk ν.modulus n) ↔
      IsCoprime n (idealGenerator ν.modulus) := by
  rw [IdealCharacter.isUnit_mk_iff_isCoprime]
  conv_lhs => rw [←span_idealGenerator ν.modulus]
  rw [Ideal.isCoprime_span_singleton_iff]

theorem elementCoeff_product_inverse_mask (η ν : Character) (n : O) :
    elementCoeff ((η.product ν).product ν.inverse) n =
      if IsCoprime n (idealGenerator ν.modulus) then elementCoeff η n else 0 := by
  rw [elementCoeff_product,elementCoeff_product,elementCoeff_inverse]
  by_cases hn : IsCoprime n (idealGenerator ν.modulus)
  · have hv : elementCoeff ν n ≠ 0 :=
      MulChar.apply_ne_zero_iff.mpr ((modulus_unit_iff ν n).mpr hn)
    simp only [hn,ite_true,mul_assoc,mul_inv_cancel₀ hv,mul_one]
  · have hv : elementCoeff ν n = 0 :=
      MulChar.map_nonunit ν.residue (fun hu=>hn ((modulus_unit_iff ν n).mp hu))
    simp only [hn,ite_false,hv,mul_zero,zero_mul]

theorem rowTwist_product (η ν : Character) (m f z n : O) :
    rowTwist (elementHom (η.product ν)) m f z n =
      rowTwist (elementHom η) m f z n * elementCoeff ν n := by
  change elementCoeff (η.product ν) n * idealRowHom (m^6*f^4*z) (Ideal.span {n}) =
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) * elementCoeff ν n
  rw [elementCoeff_product]
  ring

theorem rowTwist_product_inverse_mask (η ν : Character) (m A z n : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    rowTwist (elementHom ((η.product ν).product ν.inverse)) m 1 (A*z) n =
      rowTwist (elementHom η) (m*idealGenerator ν.modulus) 1 (A*z) n := by
  rw [row_mask_mul η m (idealGenerator ν.modulus) A z n hmLam hm2]
  change elementCoeff ((η.product ν).product ν.inverse) n *
    idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n}) = _
  rw [elementCoeff_product_inverse_mask]
  split_ifs
  · rfl
  · exact zero_mul _

theorem fixedInducingRow_product_of (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (h : FixedInducingRow η Q m A z) :
    FixedInducingRow (η.product ν) Q m A z :=
  fixedInducingRow_of_product η (η.product ν) ν Q m A z z hν
    (fun n=>rowTwist_product η ν m 1 (A*z) n) h

theorem fixedInducingRow_product_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow (η.product ν) Q m A z ↔ FixedInducingRow η Q m A z := by
  constructor
  · intro h
    have hi := fixedInducingRow_product_of (η.product ν) ν.inverse Q m A z hν h
    obtain ⟨χ,ψ,hprim,hind,hQ,hrow⟩ := hi
    apply (fixedInducingRow_mul_mask_iff η Q m (idealGenerator ν.modulus) A z
      hm (modulus_generator_ne_zero ν) hA hz hmLam hm2).mp
    exact ⟨χ,ψ,hprim,hind,hQ,fun n=>(hrow n).trans
      (rowTwist_product_inverse_mask η ν m A z n hmLam hm2)⟩
  · exact fixedInducingRow_product_of η ν Q m A z hν

theorem not_fixedInducingRow_product_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    (¬FixedInducingRow (η.product ν) Q m A z) ↔ ¬FixedInducingRow η Q m A z :=
  not_congr (fixedInducingRow_product_iff η ν Q m A z hν hm hA hz hmLam hm2)

theorem fixedInducingRow_product_inverse_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow (η.product ν.inverse) Q m A z ↔ FixedInducingRow η Q m A z :=
  fixedInducingRow_product_iff η ν.inverse Q m A z hν hm hA hz hmLam hm2

theorem not_fixedInducingRow_product_inverse_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    (¬FixedInducingRow (η.product ν.inverse) Q m A z) ↔ ¬FixedInducingRow η Q m A z :=
  not_congr (fixedInducingRow_product_inverse_iff η ν Q m A z hν hm hA hz hmLam hm2)

end SevenEighths.CenteredMomentFixedRayInducingTransport

end

end OAI

end Source1014

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceCharacters.lean; sha256: 12044cf80f4564f2efb1c221d797ae122398a774a8624e95cb58b51f36cf427c -/
section Source1015
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentFixedRayInducingTransport CenteredMomentFixedRowMask CenteredExceptionalProfile
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def relativeCharacter (η₀ : Character) (θ : RayQuotient.Characters M H) : Character :=
  (HeckeRayQuotient.character M H hH θ).product η₀.inverse

lemma relativeCharacter_ideal (η₀ : Character) (θ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (relativeCharacter M H hH η₀ θ) I=
      idealCoeff (HeckeRayQuotient.character M H hH θ) I*idealCoeff η₀.inverse I :=
  idealCoeff_product _ _ _

lemma relativeCharacter_norm (η₀ : Character) (θ : RayQuotient.Characters M H) (I : Ideal O) :
    ‖idealCoeff (relativeCharacter M H hH η₀ θ) I‖≤1 := idealCoeff_norm_le_one _ _

lemma relativeCharacter_modulus (η₀ : Character) (θ : RayQuotient.Characters M H) :
    (relativeCharacter M H hH η₀ θ).modulus.absNorm≤M.absNorm*η₀.modulus.absNorm :=
  HeckePrimeScale.product_modulus_bound _ _

lemma relativeCharacter_fixedQ (η₀ : Character) (θ : RayQuotient.Characters M H)
    (Q : Ideal O) (hQM : Q≤M) (hQη : Q≤η₀.modulus) :
    Q≤(relativeCharacter M H hH η₀ θ).modulus := le_inf hQM hQη

lemma excluded_product_ideal (χ ν : Character) (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded χ R) I*idealCoeff ν I=idealCoeff (excluded (χ.product ν) R) I := by
  rw [excluded_ideal χ R hR,excluded_ideal (χ.product ν) R hR,idealCoeff_product]
  split_ifs <;> simp

lemma sector_element {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (θ : RayQuotient.Characters M H) (n : O) :
    elementCoeff (F.character.product (relativeCharacter M H hH η₀ θ)) n=
      rowTwist (elementHom (η.product (relativeCharacter M H hH η₀ θ))) fixedBadMask 1 z n := by
  simpa only [one_mul] using CenteredMomentDetectorDictionary.product_row_presentation η F.character
    (relativeCharacter M H hH η₀ θ) fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) n

theorem sector_fixedQ_iff (η η₀ : Character) (θ : RayQuotient.Characters M H)
    (Q R : Ideal O) (z : O) (hQM : Q≤M) (hQη : Q≤η₀.modulus)
    (hR : R≠0) (hz : z≠0) :
    FixedInducingRow (η.product (relativeCharacter M H hH η₀ θ)) Q
      (fixedBadMask*idealGenerator R) 1 z ↔
    FixedInducingRow η Q (fixedBadMask*idealGenerator R) 1 z :=
  fixedInducingRow_product_iff η (relativeCharacter M H hH η₀ θ) Q
    (fixedBadMask*idealGenerator R) 1 z
    (relativeCharacter_fixedQ M H hH η₀ θ Q hQM hQη)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero R hR)) one_ne_zero hz
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _))

theorem sector_nonprincipal {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (θ : RayQuotient.Characters M H) (Q R : Ideal O)
    (hQM : Q≤M) (hQη : Q≤η₀.modulus) (hR : R≠0) (hz : z≠0)
    (hex : ¬FixedInducingRow η Q (fixedBadMask*idealGenerator R) 1 z) :
    (F.character.product (relativeCharacter M H hH η₀ θ)).residue≠1 := by
  have hbase : ¬FixedInducingRow η Q fixedBadMask 1 z := by
    intro h
    exact hex ((fixedInducingRow_mul_mask_iff η Q fixedBadMask (idealGenerator R) 1 z
      fixedBadMask_ne_zero (idealGenerator_ne_zero R hR) one_ne_zero hz
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr h)
  exact CenteredMomentRayNonprincipal.actual_row_twist_nonprincipal η F.character
    (relativeCharacter M H hH η₀ θ) Q fixedBadMask 1 z
    (by simpa only [one_mul] using F.element)
    (relativeCharacter_fixedQ M H hH η₀ θ Q hQM hQη) hbase

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1015

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceSlots.lean; sha256: c96953f7c9237f65c58a37367360c80a3617ca5f0103a081cbf56e893fc0bbf2 -/
section Source1016
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentDetectorDictionary
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

lemma averaged_sector_coefficient (χ η₀ : Character) (R : Ideal O) (hR : R≠0)
    (θ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (twistedFamily M H hH ((excluded χ R).product η₀.inverse) θ) I=
      idealCoeff (excluded (χ.product (relativeCharacter M H hH η₀ θ)) R) I := by
  simp only [twistedFamily,relativeCharacter,idealCoeff_product,excluded_ideal _ R hR]
  split_ifs <;> ring

lemma averaged_sector_polynomial (χ η₀ : Character) (R : Ideal O) (hR : R≠0)
    (θ : RayQuotient.Characters M H) (W : ℝ→ℂ) (b D σ t : ℝ) :
    primePolynomial (twistedFamily M H hH ((excluded χ R).product η₀.inverse) θ) W b D σ t=
      primePolynomial (excluded (χ.product (relativeCharacter M H hH η₀ θ)) R) W b D σ t := by
  unfold primePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [averaged_sector_coefficient M H hH χ η₀ R hR θ I]

theorem natural_relative_slot {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (R : Ideal O) (hR : R≠0) (W : ℝ→ℂ) (b D σ t v : ℝ) (hD : 0<D) :
    normalizedSlot η (fixedBadMask*idealGenerator R) 1 z (primePool M H b D)
      (fun I=>idealCoeff η₀.inverse I*annularWeight W D σ v I) t D=
      (D:ℂ)^(Complex.I*t)*((RayQuotient.classNumber M H:ℂ)⁻¹*
        ∑θ : RayQuotient.Characters M H,
          primePolynomial (excluded (F.character.product (relativeCharacter M H hH η₀ θ)) R)
            W b D σ (t+v)) := by
  rw [relative_normalizedSlot_eq_ray M H η (excluded F.character R) η₀.inverse
    (fixedBadMask*idealGenerator R) 1 z
    (by simpa only [one_mul] using F.masked_element R hR) W b D σ t v hD,
    rayPrimePolynomial_eq_average M H hH]
  congr 2
  exact Finset.sum_congr rfl (fun θ _=>averaged_sector_polynomial M H hH F.character η₀ R hR θ W b D σ (t+v))

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1016

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceProduct.lean; sha256: c06ebd5d3b18c12e2c201c072db4709865158271d49db5697a2a4c9595ef6995 -/
section Source1017
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeAnnular ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentRetainedEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot CenteredMomentSlotNormalization
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def averageWeight : ℂ := (RayQuotient.classNumber M H:ℂ)⁻¹^(Fintype.card ι)

def sectorValue (χ η₀ : Character) (R : Ideal O) (W₁ W₂ : ℝ→ℂ)
    (V : ι→ℝ→ℂ) (b P σ v : ι→ℝ) (t X₁ X₂ : ℝ)
    (θ : ι→RayQuotient.Characters M H) : ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*
    (twistedIdealSum (excluded χ R) W₁ t X₁*twistedIdealSum (excluded χ R) W₂ t X₂)*
      ∏i,(P i:ℂ)^(Complex.I*t)*
        primePolynomial (excluded (χ.product (relativeCharacter M H hH η₀ (θ i))) R)
          (V i) (b i) (P i) (σ i) (t+v i)

theorem natural_relative_product {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (R : Ideal O) (hR : R≠0) (W₁ W₂ : ℝ→ℂ)
    (V : ι→ℝ→ℂ) (b P σ v : ι→ℝ) (t X₁ X₂ : ℝ)
    (hX : 0≤X₁*X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂
      (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff η₀.inverse I*annularWeight (V i) (P i) (σ i) (v i) I) P t X₁ X₂=
      averageWeight (ι:=ι) M H*∑θ : ι→RayQuotient.Characters M H,
        sectorValue M H hH F.character η₀ R W₁ W₂ V b P σ v t X₁ X₂ θ := by
  rw [←selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ hX (fun i=>(hP i).le)]
  unfold selectedProduct
  simp_rw [F.masked_plain R hR]
  simp_rw [natural_relative_slot M H hH F η₀ R hR _ _ _ _ _ _ (hP _)]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.prod_sum,
    sectorValue,averageWeight]
  rw [←Finset.mul_sum,←Finset.mul_sum]
  ring

theorem averageWeight_mass :
    ∑_θ : ι→RayQuotient.Characters M H,‖averageWeight (ι:=ι) M H‖=1 := by
  have hc : Fintype.card (RayQuotient.Characters M H)=RayQuotient.classNumber M H :=
    RayOrthogonality.card_characters H
  have hn : (RayQuotient.classNumber M H:ℝ)≠0 := by
    exact_mod_cast (RayQuotient.classNumber_pos M H).ne'
  simp only [averageWeight,Finset.sum_const,Finset.card_univ,Fintype.card_fun,hc,
    norm_pow,norm_inv,Complex.norm_natCast,nsmul_eq_mul,Nat.cast_pow]
  rw [inv_pow,mul_inv_cancel₀ (pow_ne_zero _ hn)]

theorem sector_average_energy (f : (ι→RayQuotient.Characters M H)→ℂ) :
    ‖averageWeight (ι:=ι) M H*∑θ,f θ‖^2≤
      ∑θ,‖averageWeight (ι:=ι) M H‖*‖f θ‖^2 := by
  have hm:=averageWeight_mass (ι:=ι) M H
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hm
  have he:=CubicEisenstein.norm_sum_sq_le_card Finset.univ f
  rw [norm_mul,mul_pow]
  apply (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq
  rw [←Finset.mul_sum]
  change ‖averageWeight (ι:=ι) M H‖^2*
    ((Fintype.card (ι→RayQuotient.Characters M H):ℝ)*∑θ,‖f θ‖^2)=_
  calc
    _=‖averageWeight (ι:=ι) M H‖*((Fintype.card (ι→RayQuotient.Characters M H):ℝ)*
      ‖averageWeight (ι:=ι) M H‖)*(∑θ,‖f θ‖^2) := by ring
    _= _ := by rw [hm,mul_one]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1017

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourcePhysical.lean; sha256: b4fcb6c8e724c95c87bfe9bdaa21c39d4ebd1bf91250621c188e7933cb6f8f08 -/
section Source1018
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeAnnular ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentRetainedEnergy CenteredMomentHeckeSlots CenteredMomentPrimeSlot
open CenteredMomentDetectorDictionary
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem natural_physical_product {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (R : Ideal O) (hR : R≠0) (W₁ W₂ : ℝ→ℂ)
    (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ) (t X₁ X₂ : ℝ)
    (hX : 0≤X₁*X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η₀ (V i) (P i) (external i)) P t X₁ X₂=
      averageWeight (ι:=ι) M H*∑θ : ι→RayQuotient.Characters M H,
        sectorValue M H hH F.character η₀ R W₁ W₂ (fun i x=>conj (V i x)) b P
          (fun i=>1-(external i).re) (fun i=>-(external i).im) t X₁ X₂ θ := by
  have hslot (i : ι) : rowSlot η (fixedBadMask*idealGenerator R) 1 z
      (primePool M H (b i) (P i)) (physicalSlotCoefficient η₀ (V i) (P i) (external i)) t=
      rowSlot η (fixedBadMask*idealGenerator R) 1 z (primePool M H (b i) (P i))
        (fun I=>idealCoeff η₀.inverse I*annularWeight (fun x=>conj (V i x))
          (P i) (1-(external i).re) (-(external i).im) I) t := by
    unfold rowSlot
    apply Finset.sum_congr rfl
    intro I hI
    rw [physicalSlotCoefficient_annular η₀ (V i) (P i) (external i) I
      (Finset.mem_filter.mp hI).2.1.ne_zero (hP i)]
  simpa only [positiveSlotRow,hslot] using natural_relative_product M H hH F η₀ R hR W₁ W₂
    (fun i x=>conj (V i x)) b P (fun i=>1-(external i).re) (fun i=>-(external i).im)
    t X₁ X₂ hX hP

theorem natural_physical_energy {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (R : Ideal O) (hR : R≠0) (W₁ W₂ : ℝ→ℂ)
    (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ) (t X₁ X₂ : ℝ)
    (hX : 0≤X₁*X₂) (hP : ∀i,0<P i) :
    ‖positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η₀ (V i) (P i) (external i)) P t X₁ X₂‖^2≤
      ∑θ : ι→RayQuotient.Characters M H,‖averageWeight (ι:=ι) M H‖*
        ‖sectorValue M H hH F.character η₀ R W₁ W₂ (fun i x=>conj (V i x)) b P
          (fun i=>1-(external i).re) (fun i=>-(external i).im) t X₁ X₂ θ‖^2 := by
  rw [natural_physical_product M H hH F η₀ R hR W₁ W₂ V b P external t X₁ X₂ hX hP]
  exact sector_average_energy M H _

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1018

/- Original source: OAI/NumberTheory/DirichletL/Detector/PrimeConstants.lean; sha256: fae072691ed014ee72f8ed5b2f84529a54a03a9c114dae5b1f5caa34bb78b936 -/
section Source1019
namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def localGamma (p : O) (hp : p ≠ 0) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (r : ℕ) : ℂ :=
  ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ r)

lemma localGamma_norm_one (p : O) (hp : p ≠ 0) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r : ℕ) (hr : r ≠ 0) (hr6 : r < 6) : ‖localGamma p hp hg r‖ = 1 :=
  MixedGaussConversion.norm_localGauss p hp hg hc r hr hr6

lemma actualSextic_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) : actualSextic P hg ^ 6 = 1 :=
  (actualSextic_pow_eq_one_iff P hg hc 6).mpr (by decide)

lemma actualSextic_neg_one_sq (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) : actualSextic P hg (-1)^2 = 1 := by
  rw [← map_pow]
  norm_num

theorem localGamma_inverse_pair (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r : ℕ) (hr : r ≠ 0) (hr6 : r < 6) :
    localGamma p hp hg r * localGamma p hp hg (6-r) =
      actualSextic (Ideal.span {p}) hg (-1)^r := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  let χ := actualSextic (Ideal.span {p}) hg
  have hχ : χ^r ≠ 1 := by
    intro he
    have hd := (actualSextic_pow_eq_one_iff _ hg hc r).mp he
    exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hr) hr6) hd
  have hinv : (χ^r)⁻¹ = χ^(6-r) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, Nat.add_sub_of_le hr6.le]
    exact actualSextic_six _ hg hc
  have hψ : (quotientTrace p hp).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp
  have he := ProbeGauss.normalizedGauss_inverse_pair (χ^r) (quotientTrace p hp) hχ hψ
  rw [hinv] at he
  simp only [localGamma, ProbePhase.normalizedTraceGauss_eq_normalizedGauss]
  simpa only [MulChar.pow_apply' _ hr] using he

lemma localGamma_two_four (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    localGamma p hp hg 2 * localGamma p hp hg 4 = 1 := by
  have he := localGamma_inverse_pair p hp hg hc 2 (by decide) (by decide)
  simpa only [show 6-2=4 from rfl, actualSextic_neg_one_sq] using he

theorem localGamma_one_two_signal (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : goodLambda^2 ∣ p-1) :
    localGamma p hp hg 1 * localGamma p hp hg 2 =
      -FiniteGaussPhase.angularFactor p * MixedGaussConversion.localG p hp hg := by
  have he := breveGamma1_gamma2_eq_neg_alpha_G (Ideal.span {p}) hg hc p rfl hp hprimary
  simpa only [localGamma, ConcreteBreveE.normalizedTraceGauss, pow_one,
    breveGamma1, breveGamma2, MixedGaussConversion.localG, FiniteGaussPhase.angularFactor,
    neg_div] using he

lemma actualSextic_pow_six_mul_add (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) (r j : ℕ) :
    actualSextic P hg ^ (6*r+j) = actualSextic P hg ^ j := by
  rw [pow_add, pow_mul, actualSextic_six P hg hc, one_pow, one_mul]

lemma actualSextic_fifth_inverse (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) :
    actualSextic P hg ^ 5 = (actualSextic P hg)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ']
  exact actualSextic_six P hg hc

lemma primeGauss_inverse_pair (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) :
    primeGauss p hp χ 1 * primeGauss p hp χ⁻¹ 1 =
      χ (-1) * (Ideal.absNorm (Ideal.span {p}):ℂ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have ht := ProbeGauss.gauss_inverse_pair χ (quotientTrace p hp) hχ
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp)
  have hcard : Nat.card (O ⧸ Ideal.span {p}) = Ideal.absNorm (Ideal.span {p}) := rfl
  simpa only [primeGauss, tsum_fintype, map_one, one_mul, gaussSum,
    ← Nat.card_eq_fintype_card, hcard] using ht

end SevenEighths.ProbePrimePower
end

end OAI

end Source1019

/- Original source: OAI/NumberTheory/DirichletL/Detector/UnramifiedScalar.lean; sha256: 8a35cb162b3743b740e2aad455c0853c3e9f255a616d6705f817ba36b7606b26 -/
section Source1020
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
include hc

theorem unramified_even_kzero (r m : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+5) 0 (6*m) =
      if r+1 ≤ m then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) * ((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else 0 := by
  rw [positiveScalar_kzero, actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_left (by omega : 6 ∣ 6*r+5+1)]
  by_cases hm : r+1 ≤ m
  · rw [ite_eq_left hm, ite_eq_left (by omega), ite_eq_left (by omega), pow_succ]
    ring
  · rw [ite_eq_right hm, ite_eq_right (by omega), ite_eq_right (by omega), sub_self]

theorem unramified_squarefree_kzero (r m : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r) 0 (6*m) =
      if m=r then (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 else 0 := by
  rw [positiveScalar_kzero, actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_right (by omega : ¬6 ∣ 6*r+1), actualSextic_pow_six_mul_add _ hg hc, pow_one]
  by_cases hm : m=r
  · rw [ite_eq_left hm, ite_eq_left (by omega)]
  · rw [ite_eq_right hm, ite_eq_right (by omega)]

theorem unramified_squarefree_kone (r m : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r) 1 (6*m) =
      if r<m then
        ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
          primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1) *
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) * ((Ideal.absNorm (Ideal.span {p}):ℂ)-1))
      else 0 := by
  rw [positiveScalar_actual_table p hp hg hc]
  rw [ite_eq_right (by decide : (1:ℕ) ≠ 0)]
  by_cases hm : r<m
  · rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left hm, gaussValuationTable,
      ite_eq_left (by omega : 6 ∣ 6*r), ite_eq_left (by omega), ite_eq_left (by omega), pow_succ]
    ring
  · rw [ite_eq_right hm]
    by_cases hm0 : m=0
    · subst m
      rw [ite_eq_right (by omega)]
    · rw [ite_eq_left ⟨rfl, by omega⟩, gaussValuationTable,
        ite_eq_left (by omega : 6 ∣ 6*r), ite_eq_right (by omega), ite_eq_right (by omega), sub_self, mul_zero]

theorem unramified_odd_zero (r m k : ℕ) (d : ℕ) (hd : d=2 ∨ d=3) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+d) k (6*m) = 0 := by
  rw [positiveScalar_actual_table p hp hg hc]
  split_ifs with hk hk1
  · rw [gaussValuationTable, ite_eq_right (by rcases hd with rfl | rfl <;> omega),
      ite_eq_right (by rcases hd with rfl | rfl <;> omega)]
  · rw [gaussValuationTable, ite_eq_right (by rcases hd with rfl | rfl <;> omega),
      ite_eq_right (by rcases hd with rfl | rfl <;> omega), mul_zero]
  · rfl

theorem unramified_even_kone (r m : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+5) 1 (6*m) =
      if m=r+1 then (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+6) else 0 := by
  rw [positiveScalar_actual_table p hp hg hc, ite_eq_right (by decide : (1:ℕ) ≠ 0)]
  by_cases hm : m=r+1
  · subst m
    rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left rfl, gaussValuationTable,
      ite_eq_right (by omega : ¬6 ∣ 6*r+5), ite_eq_left (by omega),
      actualSextic_pow_six_mul_add _ hg hc, actualSextic_fifth_inverse _ hg hc]
    have hχ : actualSextic (Ideal.span {p}) hg ≠ 1 := by
      intro h
      have hpow : actualSextic (Ideal.span {p}) hg ^ 1 = 1 := by simpa using h
      have hdiv := (actualSextic_pow_eq_one_iff _ hg hc 1).mp hpow
      norm_num at hdiv
    have hi := primeGauss_inverse_pair p hp.ne_zero (actualSextic (Ideal.span {p}) hg) hχ
    have hω : actualSextic (Ideal.span {p}) hg (-1) ≠ 0 :=
      (actualSextic (Ideal.span {p}) hg).apply_ne_zero_iff.mpr (isUnit_one.neg : IsUnit (-1 : O ⧸ Ideal.span {p}))
    calc
      _ = (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) *
          ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
            (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 *
              primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg)⁻¹ 1)) := by ring
      _ = (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) * (Ideal.absNorm (Ideal.span {p}):ℂ) := by
        rw [hi]
        field_simp
      _ = _ := (pow_succ _ (6*r+5)).symm
  · rw [ite_eq_right hm]
    by_cases hm0 : m=0
    · subst m
      rw [ite_eq_right (by omega)]
    · rw [ite_eq_left ⟨rfl, by omega⟩, gaussValuationTable,
        ite_eq_right (by omega : ¬6 ∣ 6*r+5), ite_eq_right (by omega), mul_zero]

end SevenEighths.ProbePrimePower
end

end OAI

end Source1020

/- Original source: OAI/NumberTheory/DirichletL/Detector/LocalWeights.lean; sha256: 43d33e71d7c2db43c9e645e32e198c4e564b691a177c75634f9bacf0688813f2 -/
section Source1021
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma even_diagonal_exponent (r : ℕ) : r + (2*r).choose 2 = 2*r*r := by
  rw [Nat.choose_two_right, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  cases r with
  | zero => simp
  | succ r =>
    rw [show 2*(r+1)-1 = 2*r+1 by omega]
    ring

def localCubePhase (C omega : ℂ) (e l k : ℕ) : ℂ :=
  C^l * omega^((e+3*l)*k+e*l+l.choose 2)

theorem localCubePhase_even (C omega : ℂ) (hC : C^2=omega) (ho : omega^2=1)
    (e r k : ℕ) : localCubePhase C omega e (2*r) k = omega^(e*k) := by
  unfold localCubePhase
  rw [pow_mul C 2 r, hC, ← pow_add]
  have he : r+((e+3*(2*r))*k+e*(2*r)+(2*r).choose 2) =
      e*k+2*(3*r*k+e*r+r*r) := by
    have hd := even_diagonal_exponent r
    nlinarith
  rw [he, pow_add, pow_mul omega 2, ho, one_pow, mul_one]

def weightedScalar (Q eta a G1 C omega X W V scalar : ℂ) (e l k m : ℕ) : ℂ :=
  (-eta*X/G1)^e * (a*X^3/Q)^l * localCubePhase C omega e l k * scalar * W^k * V^m

lemma weightedScalar_zero (Q eta a G1 C omega X W V : ℂ) (e l k m : ℕ) :
    weightedScalar Q eta a G1 C omega X W V 0 e l k m = 0 := by
  simp [weightedScalar]

def evenRatio (Q a X V : ℂ) : ℂ := a^2*Q^4*X^6*V

lemma weighted_squarefree_boundary (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hG : G1 ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r)*G1) 1 (2*r) 0 r =
      evenRatio Q a X V ^ r * (-eta*X) := by
  unfold weightedScalar
  rw [localCubePhase_even C omega hC ho]
  simp only [mul_zero, pow_zero, pow_one, mul_one]
  unfold evenRatio
  rw [mul_pow, mul_pow, mul_pow, div_pow, mul_pow, pow_mul, pow_mul, pow_mul, pow_mul]
  field_simp
  ring

lemma weighted_even_bulk (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r d : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r+5)*(Q-1))
      0 (2*r+2) 0 (r+1+d) =
      evenRatio Q a X V ^ r * (evenRatio Q a X V*(1-Q⁻¹)*V^d) := by
  unfold weightedScalar
  rw [show 2*r+2=2*(r+1) by ring, localCubePhase_even C omega hC ho]
  simp only [zero_mul, pow_zero, one_mul, mul_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

lemma weighted_even_kone (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r+6))
      0 (2*r+2) 1 (r+1) = evenRatio Q a X V ^ r * (W*evenRatio Q a X V) := by
  unfold weightedScalar
  rw [show 2*r+2=2*(r+1) by ring, localCubePhase_even C omega hC ho]
  simp only [pow_zero, pow_one, one_mul, mul_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

lemma weighted_squarefree_bulk (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hG : G1 ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r d : ℕ) :
    weightedScalar Q eta a G1 C omega X W V
      ((omega⁻¹*G1)*(Q^(6*r)*(Q-1))) 1 (2*r) 1 (r+1+d) =
      evenRatio Q a X V ^ r * (-eta*(Q-1)*X*W*V^(d+1)) := by
  have hω : omega ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at ho; norm_num at ho
  unfold weightedScalar
  rw [localCubePhase_even C omega hC ho]
  simp only [one_mul, pow_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

end SevenEighths.ProbeEuler
end

end OAI

end Source1021

/- Original source: OAI/NumberTheory/DirichletL/Detector/LocalSeries.lean; sha256: 95f67efdc7a20e4bb253a427183e8be324914747e1147e36772ca5dc67b0c306 -/
section Source1022
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalMarkedTerm (eta a X W V : ℂ) (e l k m : ℕ) : ℂ :=
  if e+3*l=0 then 0 else
    weightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1)) X W V
      (positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (e+3*l-1) k (6*m)) e l k m

include hc in
lemma localGamma_conjugate_three_sq :
    (star (localGamma p hp.ne_zero hg 3))^2 = actualSextic (Ideal.span {p}) hg (-1) := by
  have hg3 : localGamma p hp.ne_zero hg 3 ^ 2 = actualSextic (Ideal.span {p}) hg (-1) :=
    ProbePhase.normalizedTraceGauss_three_sq p hp.ne_zero hg hc
  rw [← star_pow, hg3]
  have hω := actualSextic_neg_one_sq (Ideal.span {p}) hg
  rcases (sq_eq_one_iff).mp hω with h | h
  · simp [h]
  · simp [h]

include hc in
lemma firstGauss_ne_zero : primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 ≠ 0 := by
  have hχ : actualSextic (Ideal.span {p}) hg ≠ 1 := by
    intro h
    have he : actualSextic (Ideal.span {p}) hg ^ 1 = 1 := by simpa using h
    have hd := (actualSextic_pow_eq_one_iff _ hg hc 1).mp he
    norm_num at hd
  have he := primeGauss_inverse_pair p hp.ne_zero (actualSextic (Ideal.span {p}) hg) hχ
  have hω : actualSextic (Ideal.span {p}) hg (-1) ≠ 0 :=
    (actualSextic (Ideal.span {p}) hg).apply_ne_zero_iff.mpr isUnit_one.neg
  have hQ : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  intro hz
  rw [hz, zero_mul] at he
  exact (mul_ne_zero hω hQ) he.symm

omit [(Ideal.span {p}).IsMaximal] in
include hp in
lemma primeNorm_ne_zero : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
  exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)

include hc

omit hc in
@[simp] theorem markedTerm_zero_index (eta a X W V : ℂ) (k m : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 0 0 k m = 0 := by
  simp only [principalMarkedTerm, mul_zero, add_zero, ite_true]

omit hc in
lemma markedTerm_higher_outer (eta a X W V : ℂ) (e l k m : ℕ) :
    principalMarkedTerm p hp hg eta a X W V e l (k+2) m = 0 := by
  unfold principalMarkedTerm
  split_ifs
  · rfl
  · rw [positiveScalar_kge_two p hp, weightedScalar_zero]

lemma markedTerm_odd (eta a X W V : ℂ) (e r k m : ℕ) (he : e ≤ 1) :
    principalMarkedTerm p hp hg eta a X W V e (2*r+1) k m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega)]
  have hn : e+3*(2*r+1)-1 = 6*r+(e+2) := by omega
  rw [hn, unramified_odd_zero p hp hg hc r m k (e+2) (by omega), weightedScalar_zero]

lemma markedTerm_squarefree_boundary (eta a X W V : ℂ) (r : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 0 r =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r * (-eta*X) := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kzero p hp hg hc, ite_eq_left rfl]
  exact weighted_squarefree_boundary _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (firstGauss_ne_zero p hp hg hc) (localGamma_conjugate_three_sq p hp hg hc)
    (actualSextic_neg_one_sq _ hg) r

lemma markedTerm_squarefree_boundary_off (eta a X W V : ℂ) (r m : ℕ) (hm : m ≠ r) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 0 m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kzero p hp hg hc, ite_eq_right hm, weightedScalar_zero]

lemma markedTerm_even_bulk (eta a X W V : ℂ) (r d : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 0 (r+1+d) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*V^d) := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kzero p hp hg hc, ite_eq_left (by omega)]
  exact weighted_even_bulk _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (localGamma_conjugate_three_sq p hp hg hc) (actualSextic_neg_one_sq _ hg) r d

lemma markedTerm_even_bulk_off (eta a X W V : ℂ) (r m : ℕ) (hm : m < r+1) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 0 m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kzero p hp hg hc, ite_eq_right (by omega), weightedScalar_zero]

lemma markedTerm_even_kone (eta a X W V : ℂ) (r : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 1 (r+1) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kone p hp hg hc, ite_eq_left rfl]
  exact weighted_even_kone _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (localGamma_conjugate_three_sq p hp hg hc) (actualSextic_neg_one_sq _ hg) r

lemma markedTerm_even_kone_off (eta a X W V : ℂ) (r m : ℕ) (hm : m ≠ r+1) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 1 m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kone p hp hg hc, ite_eq_right hm, weightedScalar_zero]

lemma markedTerm_squarefree_bulk (eta a X W V : ℂ) (r d : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 1 (r+1+d) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V^(d+1)) := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kone p hp hg hc, ite_eq_left (by omega)]
  exact weighted_squarefree_bulk _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (firstGauss_ne_zero p hp hg hc) (localGamma_conjugate_three_sq p hp hg hc)
    (actualSextic_neg_one_sq _ hg) r d

lemma markedTerm_squarefree_bulk_off (eta a X W V : ℂ) (r m : ℕ) (hm : m < r+1) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 1 m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kone p hp hg hc, ite_eq_right (by omega), weightedScalar_zero]

end SevenEighths.ProbeEuler
end

end OAI

end Source1022

/- Original source: OAI/NumberTheory/DirichletL/Detector/Euler.lean; sha256: 1bd3365ab3804e359606f209ce9d95853c118cb69f5d7379a7073ef1e02d6bd3 -/
section Source1023
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

def markedFactor (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ((R * (1 - qInv) - K * V ^ a) / (1 - V) + J) / (1 - R)

def markedTableSeries (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ∑' r : ℕ, R ^ r *
    ((∑' m : ℕ, (R * (1 - qInv) * V ^ m - K * V ^ (m + a))) + J)

theorem marked_table_resummation (R V qInv K J : ℂ) (a : ℕ)
    (hR : ‖R‖ < 1) (hV : ‖V‖ < 1) :
    markedTableSeries R V qInv K J a = markedFactor R V qInv K J a := by
  have hgeo := hasSum_geometric_of_norm_lt_one hV
  have hfirst := hgeo.mul_left (R * (1 - qInv))
  have hsecond : HasSum (fun m : ℕ => K * V ^ (m + a))
      (K * V ^ a * (1 - V)⁻¹) := by
    convert hgeo.mul_left (K * V ^ a) using 1
    funext m
    rw [pow_add]
    ring
  have hin := (hfirst.sub hsecond).tsum_eq
  unfold markedTableSeries
  rw [hin, tsum_mul_right, tsum_geometric_of_norm_lt_one hR]
  unfold markedFactor
  simp only [div_eq_mul_inv]
  ring

theorem unramified_marked_error (R V qInv K W D : ℂ)
    (hR : 1 - R ≠ 0) (hV : 1 - V ≠ 0) :
    markedFactor R V qInv K (-D + W * R) 1 + D =
      (R * ((1 - qInv) + (1 - V) * (W - D)) - K * V) /
        ((1 - R) * (1 - V)) := by
  unfold markedFactor
  field_simp
  ring

end SevenEighths.ProbeEuler
end

end OAI

end Source1023

/- Original source: OAI/NumberTheory/DirichletL/Detector/LocalSummation.lean; sha256: 9a954d140811c6fa818b438ce507688a6890f439271d5141278920e221c5dabf -/
section Source1024
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma hasSum_geometric_tail (f : ℕ → ℂ) (a : ℕ) (B V : ℂ) (hV : ‖V‖<1)
    (hz : ∀ m, m<a → f m=0) (hf : ∀ n, f (n+a)=B*V^n) :
    HasSum f (B/(1-V)) := by
  have ht : HasSum (fun n => f (n+a)) (B/(1-V)) := by
    simpa only [hf, div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hV).mul_left B
  have hs : (∑ i ∈ Finset.range a, f i) = 0 :=
    Finset.sum_eq_zero (fun i hi => hz i (Finset.mem_range.mp hi))
  simpa only [hs, zero_add] using ht.sum_range_add

lemma tsum_two_of_rest_zero (f : ℕ → ℂ) (hf : ∀ k, f (k+2)=0) :
    (∑' k, f k) = f 0+f 1 := by
  rw [tsum_eq_sum (s := {0,1})]
  · simp
  · intro k hk
    have hk2 : 2 ≤ k := by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk; omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hk2
    simpa only [Nat.add_comm] using hf k

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalInner (eta a X W V : ℂ) (e l : ℕ) : ℂ :=
  ∑' k : ℕ, ∑' m : ℕ, principalMarkedTerm p hp hg eta a X W V e l k m

include hc

lemma squarefree_boundary_hasSum (eta a X W V : ℂ) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 1 (2*r) 0 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r * (-eta*X)) := by
  apply (hasSum_ite_eq r _).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hmS
  dsimp only
  by_cases hm : m=r
  · subst m
    rw [ite_eq_left rfl, markedTerm_squarefree_boundary p hp hg hc]
  · rw [ite_eq_right hm, markedTerm_squarefree_boundary_off p hp hg hc _ _ _ _ _ _ _ hm]

lemma even_kone_hasSum (eta a X W V : ℂ) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 1 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  apply (hasSum_ite_eq (r+1) _).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hmS
  dsimp only
  by_cases hm : m=r+1
  · subst m
    rw [ite_eq_left rfl, markedTerm_even_kone p hp hg hc]
  · rw [ite_eq_right hm, markedTerm_even_kone_off p hp hg hc _ _ _ _ _ _ _ hm]

lemma even_bulk_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 0 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)) / (1-V)) := by
  apply hasSum_geometric_tail _ (r+1) _ V hV
  · exact markedTerm_even_bulk_off p hp hg hc eta a X W V r
  · intro n
    rw [Nat.add_comm n (r+1), markedTerm_even_bulk p hp hg hc]
    ring

lemma squarefree_bulk_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 1 (2*r) 1 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V) / (1-V)) := by
  apply hasSum_geometric_tail _ (r+1) _ V hV
  · exact markedTerm_squarefree_bulk_off p hp hg hc eta a X W V r
  · intro n
    rw [Nat.add_comm n (r+1), markedTerm_squarefree_bulk p hp hg hc, pow_succ]
    ring

omit hc in
lemma principalInner_two (eta a X W V : ℂ) (e l : ℕ) :
    principalInner p hp hg eta a X W V e l =
      (∑' m, principalMarkedTerm p hp hg eta a X W V e l 0 m) +
      (∑' m, principalMarkedTerm p hp hg eta a X W V e l 1 m) := by
  apply tsum_two_of_rest_zero
  intro k
  simp only [markedTerm_higher_outer p hp hg, tsum_zero]

lemma principalInner_squarefree (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    principalInner p hp hg eta a X W V 1 (2*r) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (-eta*X - eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V/(1-V)) := by
  rw [principalInner_two p hp hg, (squarefree_boundary_hasSum p hp hg hc _ _ _ _ _ r).tsum_eq,
    (squarefree_bulk_hasSum p hp hg hc _ _ _ _ _ hV r).tsum_eq]
  ring

lemma principalInner_even (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    principalInner p hp hg eta a X W V 0 (2*r+2) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)/(1-V) +
          W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) := by
  rw [principalInner_two p hp hg, (even_bulk_hasSum p hp hg hc _ _ _ _ _ hV r).tsum_eq,
    (even_kone_hasSum p hp hg hc _ _ _ _ _ r).tsum_eq]
  ring

lemma principalInner_odd (eta a X W V : ℂ) (e r : ℕ) (he : e≤1) :
    principalInner p hp hg eta a X W V e (2*r+1) = 0 := by
  simp only [principalInner, markedTerm_odd p hp hg hc _ _ _ _ _ e r _ _ he, tsum_zero]

omit hc in
@[simp] lemma principalInner_zero (eta a X W V : ℂ) :
    principalInner p hp hg eta a X W V 0 0 = 0 := by
  simp only [principalInner, markedTerm_zero_index p hp hg, tsum_zero]

lemma principalInner_squarefree_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    HasSum (fun l => principalInner p hp hg eta a X W V 1 l)
      ((-eta*X-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V/(1-V)) /
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  let B := -eta*X-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V/(1-V)
  have he : HasSum (fun r => principalInner p hp hg eta a X W V 1 (2*r))
      ((1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)⁻¹ * B) := by
    simpa only [principalInner_squarefree p hp hg hc eta a X W V hV, B] using
      (hasSum_geometric_of_norm_lt_one hR).mul_right B
  have ho : HasSum (fun r => principalInner p hp hg eta a X W V 1 (2*r+1)) 0 := by
    simp only [principalInner_odd p hp hg hc eta a X W V 1 _ (by omega)]
    exact hasSum_zero
  convert he.even_add_odd ho using 1
  simp only [add_zero, div_eq_mul_inv, B]
  ring

lemma principalInner_even_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    HasSum (fun l => principalInner p hp hg eta a X W V 0 l)
      ((evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)/(1-V) +
          W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) /
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  let B := evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)/(1-V) +
          W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V
  have he : HasSum (fun r => principalInner p hp hg eta a X W V 0 (2*r))
      (B/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    apply hasSum_geometric_tail _ 1 B _ hR
    · intro m hm
      have hm0 : m=0 := by omega
      simp [hm0, principalInner_zero p hp hg]
    · intro r
      rw [show 2*(r+1)=2*r+2 by ring, principalInner_even p hp hg hc _ _ _ _ _ hV]
      ring
  have ho : HasSum (fun r => principalInner p hp hg eta a X W V 0 (2*r+1)) 0 := by
    simp only [principalInner_odd p hp hg hc eta a X W V 0 _ (by omega)]
    exact hasSum_zero
  simpa only [add_zero, B] using he.even_add_odd ho

def principalMarkedSeries (eta a X W V : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l : ℕ, principalInner p hp hg eta a X W V e.val l

theorem principalMarkedSeries_eq (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    principalMarkedSeries p hp hg eta a X W V =
      markedFactor (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) V
        (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹
        (eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W)
        (-eta*X+W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) 1 := by
  unfold principalMarkedSeries
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [(principalInner_even_hasSum p hp hg hc eta a X W V hV hR).tsum_eq,
    (principalInner_squarefree_hasSum p hp hg hc eta a X W V hV hR).tsum_eq]
  unfold markedFactor
  simp only [pow_one]
  ring

end SevenEighths.ProbeEuler
end

end OAI

end Source1024

/- Original source: OAI/NumberTheory/DirichletL/Detector/Local.lean; sha256: c24d3484b46dc6fb5dab01bd154b0a9b666750565ebf1af7dd12631ad9a55003 -/
section Source1025
namespace OAI

namespace SevenEighths.ProbeLocal
noncomputable section

def localFactor (V W Pstar : ℂ) : ℂ := 1 / (1 - V) + W / (1 - W) + Pstar

def localCorrection (V W D Pstar : ℂ) : ℂ :=
  localFactor V W Pstar * ((1 - V) * (1 - W)) / (1 - D)

def continuedCorrection (V W D Pstar : ℂ) : ℂ :=
  (1 - V * W + (1 - V) * (1 - W) * Pstar) / (1 - D)

theorem continuedCorrection_eq_raw (V W D Pstar : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar = localCorrection V W D Pstar := by
  unfold continuedCorrection localCorrection localFactor
  field_simp
  ring

def compensatedReplacement (V W D Pstar B q : ℂ) : ℂ :=
  ((B - q) * (1 - V) * (1 - W) * Pstar - q * (1 - V * W)) / (1 - D)

theorem correction_defect (V W D Pstar : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0) :
    localCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold localCorrection localFactor
  field_simp
  ring

theorem compensatedReplacement_eq_raw (V W D Pstar B q : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0)
    (hP : localFactor V W Pstar ≠ 0) :
    compensatedReplacement V W D Pstar B q =
      localCorrection V W D Pstar * (B * Pstar / localFactor V W Pstar - q) := by
  unfold localCorrection compensatedReplacement
  field_simp
  unfold localFactor
  field_simp
  ring

theorem compensatedReplacement_ramified (V Pstar B q : ℂ) (hV : 1 - V ≠ 0) :
    compensatedReplacement V 0 0 Pstar B q =
      B * (1 - V) * Pstar - q * localCorrection V 0 0 Pstar := by
  unfold compensatedReplacement localCorrection localFactor
  field_simp
  ring

theorem normalized_cancellation (V W D Pstar B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D Pstar B q +
        localCorrection V W D Pstar * vInv =
      (1 - V) * (1 - W) / (1 - D) *
        ((vInv - q) * (V / (1 - V) - D) +
          (B + vInv - q) * (Pstar + D)) := by
  unfold compensatedReplacement localCorrection localFactor
  field_simp
  linear_combination -(1 - V) * (1 - W) * hBD + (1 - V) * hvW

theorem continuedCorrection_defect (V W D Pstar : ℂ) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold continuedCorrection
  field_simp
  ring

theorem continued_normalized_cancellation (V W D Pstar B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D Pstar B q +
        continuedCorrection V W D Pstar * vInv =
      (1 - V) * (1 - W) / (1 - D) *
        ((vInv - q) * (V / (1 - V) - D) +
          (B + vInv - q) * (Pstar + D)) := by
  unfold compensatedReplacement continuedCorrection
  field_simp
  linear_combination -(1 - V) * (1 - W) * hBD + (1 - V) * hvW

theorem continued_ramified_compensation (V Pstar B q : ℂ) :
    compensatedReplacement V 0 0 Pstar B q =
      B * (1 - V) * Pstar - q * continuedCorrection V 0 0 Pstar := by
  simp only [compensatedReplacement, continuedCorrection, mul_zero, sub_zero,
    mul_one, div_one]
  ring

end
end SevenEighths.ProbeLocal

end OAI

end Source1025

/- Original source: OAI/NumberTheory/DirichletL/Detector/CorrectionBounds.lean; sha256: 6531ff6a758f9cbda74d5be18ac98ce0e65e9a4d1a9dae7008add6d372029c7e -/
section Source1026
namespace OAI

noncomputable section
namespace SevenEighths.ProbeLocal

lemma one_sub_ne_zero_of_norm_le_half (a : ℂ) (ha : ‖a‖ ≤ 1/2) : 1 - a ≠ 0 := by
  intro h
  have : a = 1 := by linear_combination -h
  rw [this, norm_one] at ha
  norm_num at ha

lemma inv_one_sub_norm_le_two (a : ℂ) (ha : ‖a‖ ≤ 1/2) : ‖(1-a)⁻¹‖ ≤ 2 := by
  have hl := norm_sub_norm_le (1 : ℂ) a
  simp only [norm_one] at hl
  have hd : 0 < ‖1-a‖ := by linarith
  rw [norm_inv, ← one_div, div_le_iff₀ hd]
  linarith

theorem unramified_marked_error_bound (R V qInv K W D : ℂ)
    (hR : ‖R‖ ≤ 1/2) (hV : ‖V‖ ≤ 1/2) (hq : ‖qInv‖ ≤ 1) (hD : ‖D‖ ≤ 1/2) :
    ‖ProbeEuler.markedFactor R V qInv K (-D + W*R) 1 + D‖ ≤
      12 * ‖R‖ * (1 + ‖W‖) + 4 * ‖K‖ * ‖V‖ := by
  rw [ProbeEuler.unramified_marked_error R V qInv K W D
    (one_sub_ne_zero_of_norm_le_half R hR) (one_sub_ne_zero_of_norm_le_half V hV),
    div_eq_mul_inv, mul_inv, norm_mul, norm_mul]
  have hnum : ‖R*((1-qInv)+(1-V)*(W-D))-K*V‖ ≤
      ‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖ := by
    calc
      _ ≤ ‖R*((1-qInv)+(1-V)*(W-D))‖ + ‖K*V‖ := norm_sub_le _ _
      _ = ‖R‖ * ‖(1-qInv)+(1-V)*(W-D)‖ + ‖K‖*‖V‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖R‖ * (‖1-qInv‖ + ‖1-V‖*‖W-D‖) + ‖K‖*‖V‖ := by
        gcongr
        simpa only [norm_mul] using norm_add_le (1-qInv) ((1-V)*(W-D))
      _ ≤ ‖R‖ * (2 + (1+‖V‖)*(‖W‖+‖D‖)) + ‖K‖*‖V‖ := by
        gcongr
        · calc ‖1-qInv‖ ≤ ‖(1:ℂ)‖+‖qInv‖ := norm_sub_le _ _
               _ ≤ 2 := by simp only [norm_one]; linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) V
        · exact norm_sub_le W D
  have hv := inv_one_sub_norm_le_two V hV
  have hr := inv_one_sub_norm_le_two R hR
  calc
    _ ≤ (‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖) * (2*2) := by
      gcongr
    _ ≤ 12 * ‖R‖ * (1+‖W‖) + 4*‖K‖*‖V‖ := by
      have he : 2 + (1+‖V‖)*(‖W‖+‖D‖) ≤ 3*(1+‖W‖) := by
        have : (1+‖V‖)*(‖W‖+‖D‖) ≤ (3/2:ℝ)*(‖W‖+1/2) := by gcongr ; linarith
        nlinarith [norm_nonneg W]
      nlinarith [mul_le_mul_of_nonneg_left he (norm_nonneg R)]

theorem continuedCorrection_defect_bound (V W D Pstar : ℂ)
    (hV : ‖V‖ ≤ 1/2) (hD : ‖D‖ ≤ 1/2) :
    ‖continuedCorrection V W D Pstar - 1‖ ≤
      2 * (‖D‖ * (‖V‖+‖W‖+‖V‖*‖W‖) + ‖V‖*‖W‖ +
        2*(1+‖W‖)*‖Pstar+D‖) := by
  rw [continuedCorrection_defect _ _ _ _ (one_sub_ne_zero_of_norm_le_half D hD),
    div_eq_mul_inv, norm_mul]
  have hA : ‖V+W-V*W‖ ≤ ‖V‖+‖W‖+‖V‖*‖W‖ := by
    calc
      _ ≤ ‖V+W‖+‖V*W‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_mul]; gcongr; exact norm_add_le V W
  have hnum : ‖D*(V+W-V*W)-V*W+(1-V)*(1-W)*(Pstar+D)‖ ≤
      ‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖ := by
    calc
      _ ≤ ‖D*(V+W-V*W)-V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := norm_add_le _ _
      _ ≤ ‖D*(V+W-V*W)‖+‖V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖D‖*‖V+W-V*W‖+‖V‖*‖W‖+‖1-V‖*‖1-W‖*‖Pstar+D‖ := by simp only [norm_mul]
      _ ≤ _ := by
        gcongr
        · calc ‖1-V‖ ≤ 1+‖V‖ := by simpa only [norm_one] using norm_sub_le (1:ℂ) V
               _ ≤ 2 := by linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) W
  calc
    _ ≤ (‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖)*2 := by
      gcongr
      exact inv_one_sub_norm_le_two D hD
    _ = _ := by ring

end SevenEighths.ProbeLocal
end

end OAI

end Source1026

/- Original source: OAI/NumberTheory/DirichletL/Detector/EulerCoordinates.lean; sha256: 3c3a1b462473693820fd0a530b1b3a860b9b55fec2b2e38ebabf543ffc3a2943 -/
section Source1027
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

def coordV (Q : ℝ) (z : ℂ) : ℂ := (Q : ℂ) ^ (-6*z)
def coordR (Q : ℝ) (A x z : ℂ) : ℂ := A * (Q : ℂ) ^ (4-6*x-6*z)
def coordW (Q : ℝ) (v w : ℂ) : ℂ := v * (Q : ℂ) ^ (-w)
def coordD (Q : ℝ) (eta v x : ℂ) : ℂ := eta * star v * (Q : ℂ) ^ (-x)
def coordK (Q : ℝ) (eta x w : ℂ) : ℂ := eta * (Q-1) * (Q : ℂ) ^ (-x-w)

def unramifiedClosed (Q : ℝ) (A eta v x w z : ℂ) : ℂ :=
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  ProbeLocal.continuedCorrection V W D (markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1)

def actualAPhase (eta : HeckeFamily.Character) (p : O) : ℂ :=
  star (FiniteGaussPhase.angularFactor p) ^ 6 * HeckeFamily.elementCoeff eta p ^ 6

def actualUnramifiedClosed (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p}) (x w z : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm (Ideal.span {p})) (actualAPhase eta p)
    (HeckeFamily.elementCoeff eta p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u)) x w z

lemma actualAPhase_norm_le_one (eta : HeckeFamily.Character) (p : O) :
    ‖actualAPhase eta p‖ ≤ 1 := by
  simp only [actualAPhase, norm_mul, norm_pow, norm_star]
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) (CompletedGauss.angularFactor_norm_le_one p))).trans
    (pow_le_one₀ (norm_nonneg _) (ProbeRow.targetMonoid_norm_le_one eta p))

lemma coordV_norm (Q : ℝ) (hQ : 0 < Q) (z : ℂ) :
    ‖coordV Q z‖ = Q ^ (-6*z.re) := by
  rw [coordV, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp

lemma coordR_norm_le (Q : ℝ) (hQ : 0 < Q) (A x z : ℂ) (hA : ‖A‖ ≤ 1) :
    ‖coordR Q A x z‖ ≤ Q ^ (4-6*x.re-6*z.re) := by
  rw [coordR, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hA

lemma coordW_norm_le (Q : ℝ) (hQ : 0 < Q) (v w : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖coordW Q v w‖ ≤ Q ^ (-w.re) := by
  rw [coordW, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hv

lemma coordD_norm_le (Q : ℝ) (hQ : 0 < Q) (eta v x : ℂ)
    (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖coordD Q eta v x‖ ≤ Q ^ (-x.re) := by
  rw [coordD, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  apply mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _)
  rw [norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) he).trans hv

lemma coordK_norm_le (Q : ℝ) (hQ : 1 ≤ Q) (eta x w : ℂ) (he : ‖eta‖ ≤ 1) :
    ‖coordK Q eta x w‖ ≤ Q ^ (1-x.re-w.re) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hsub : ‖(Q:ℂ)-1‖ = Q-1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hQ)]
  rw [coordK, norm_mul, norm_mul, hsub, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
  have heq : (1-x.re-w.re) = 1 + (-x.re-w.re) := by ring
  rw [heq, Real.rpow_add hQ0, Real.rpow_one]
  simp only [Complex.sub_re, Complex.neg_re]
  gcongr
  calc ‖eta‖*(Q-1) ≤ 1*(Q-1) := mul_le_mul_of_nonneg_right he (sub_nonneg.mpr hQ)
       _ ≤ Q := by linarith

end SevenEighths.ProbeEuler
end

end OAI

end Source1027

/- Original source: OAI/NumberTheory/DirichletL/Detector/PrincipalEulerIdentity.lean; sha256: 8edd1fc6579727fc2ab6ac39dd467b89840ba43f26bf48a6201d2cc5e8515e0d -/
section Source1028
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma evenRatio_eq_coordR (Q : ℝ) (hQ : 0<Q) (a x z : ℂ) :
    evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z) = coordR Q (a^2) x z := by
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold evenRatio coordR coordV
  calc
    _ = a^2 * ((Q:ℂ)^4 * ((Q:ℂ)^(-x))^6 * (Q:ℂ)^(-6*z)) := by ring
    _ = a^2 * ((Q:ℂ)^(4:ℂ) * (Q:ℂ)^((6:ℂ)*(-x)) * (Q:ℂ)^(-6*z)) := by
      rw [Complex.cpow_ofNat]
      have h6 : (Q:ℂ)^((6:ℂ)*(-x)) = ((Q:ℂ)^(-x))^6 := by
        simpa using Complex.cpow_nat_mul (Q:ℂ) 6 (-x)
      rw [h6]
    _ = a^2 * (Q:ℂ)^((4:ℂ)+6*(-x)+(-6*z)) := by
      rw [← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
    _ = _ := by congr 2; ring

lemma coordK_eq_geometric (Q : ℝ) (hQ : 0<Q) (eta x w : ℂ) :
    coordK Q eta x w = eta*((Q:ℂ)-1)*((Q:ℂ)^(-x))*((Q:ℂ)^(-w)) := by
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold coordK
  rw [show -x-w = -x+(-w) by ring, Complex.cpow_add _ _ hn]
  ring

lemma one_sub_ne_zero_of_norm_lt_one (a : ℂ) (ha : ‖a‖<1) : 1-a ≠ 0 := by
  intro h
  have he : a=1 := by linear_combination -h
  rw [he, norm_one] at ha
  exact lt_irrefl _ ha

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalFullSeries (eta a X W V : ℂ) : ℂ :=
  1/(1-V)+W/(1-W)+principalMarkedSeries p hp hg eta a X W V

include hc

theorem principalFullSeries_euler_identity (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta 1 x ≠ 0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    principalFullSeries p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) =
      (1-coordD Q eta 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q (a^2) eta 1 x w z := by
  dsimp only
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  simp only [Complex.ofReal_natCast]
  have hratio := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a x z
  simp only [Complex.ofReal_natCast] at hratio
  have hr : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hratio]
    exact hR
  rw [principalFullSeries, principalMarkedSeries_eq p hp hg hc _ _ _ _ _ hV hr,
    hratio]
  unfold unramifiedClosed
  dsimp only
  rw [coordK_eq_geometric _ hQ]
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hw := one_sub_ne_zero_of_norm_lt_one _ hW
  simp only [coordW, coordD, star_one, mul_one, one_mul, Complex.ofReal_natCast] at hD hw ⊢
  unfold ProbeLocal.continuedCorrection
  field_simp [hD, hv, hw]
  ring

omit hc

def actualACube (eta : HeckeFamily.Character) (p : O) : ℂ :=
  star (FiniteGaussPhase.angularFactor p)^3 * HeckeFamily.elementCoeff eta p^3

lemma actualACube_sq (eta : HeckeFamily.Character) (p : O) :
    actualACube eta p ^ 2 = actualAPhase eta p := by
  unfold actualACube actualAPhase
  ring

end SevenEighths.ProbeEuler
end

end OAI

end Source1028

/- Original source: OAI/NumberTheory/DirichletL/Detector/SpectralWeights.lean; sha256: 58508eda082dfdc1fd9df3cad1e204adacc1edb8bc0bd15b959ab8e3cd37602b -/
section Source1029
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma signed_diagonal_phase (omega : ℂ) (ho : omega^2=1) (e l k : ℕ) :
    omega^(((e+3*l)*k:ℕ):ℤ) * omega^(-((e*l+l.choose 2:ℕ):ℤ)) =
      omega^((e+3*l)*k+e*l+l.choose 2) := by
  have hn : omega≠0 := by intro h; simp [h] at ho
  have hi : omega⁻¹=omega := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using ho
  rw [zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, hi, ← pow_add]
  congr 1
  omega

lemma source_signed_phase (C omega : ℂ) (ho : omega^2=1) (e l k : ℕ) :
    C^l * omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ)) =
      localCubePhase C omega e l k := by
  have hn : omega≠0 := by intro h; simp [h] at ho
  rw [sub_eq_add_neg, zpow_add₀ hn, signed_diagonal_phase omega ho]
  rfl

lemma spectral_power_split (Q : ℝ) (hQ : 0<Q) (x w z : ℂ) (e l k m : ℕ) :
    (Q:ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
      ((Q:ℂ)^(-x)/(Q:ℂ)^(1/2:ℂ))^e *
      (((Q:ℂ)^(-x))^3/(Q:ℂ))^l * ((Q:ℂ)^(-w))^k * ((Q:ℂ)^(-6*z))^m := by
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  have h1 : (Q:ℂ)^(-x)/(Q:ℂ)^(1/2:ℂ) = (Q:ℂ)^(-x-(1/2:ℂ)) :=
    (Complex.cpow_sub _ _ hn).symm
  have h3 : ((Q:ℂ)^(-x))^3/(Q:ℂ) = (Q:ℂ)^(-1-3*x) := by
    rw [← Complex.cpow_nat_mul (Q:ℂ) 3 (-x)]
    calc
      _ = (Q:ℂ)^(3*(-x)) / (Q:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]; norm_num
      _ = (Q:ℂ)^(3*(-x)-1) := (Complex.cpow_sub _ _ hn).symm
      _ = _ := by congr 1; ring
  rw [h1, h3, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
    ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
    ← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
  congr 1
  ring

lemma cpow_half_eq_sqrt (Q : ℝ) (hQ : 0≤Q) :
    (Q:ℂ)^(1/2:ℂ) = (Real.sqrt Q:ℂ) := by
  rw [Real.sqrt_eq_rpow]
  simpa using (Complex.ofReal_cpow hQ (1/2:ℝ)).symm

def sourceWeightedScalar (Q : ℝ) (eta a gamma1 C omega x w z scalar : ℂ)
    (e l k m : ℕ) : ℂ :=
  (-1:ℂ)^e * gamma1^(-(e:ℤ)) * eta^e * (a*C)^l *
    omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ)) * scalar *
    (Q:ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ))

theorem sourceWeightedScalar_eq (Q : ℝ) (hQ : 0<Q)
    (eta a gamma1 G1 C omega x w z scalar : ℂ) (hG : G1=gamma1*(Real.sqrt Q:ℂ))
    (ho : omega^2=1) (e l k m : ℕ) :
    sourceWeightedScalar Q eta a gamma1 C omega x w z scalar e l k m =
      weightedScalar Q eta a G1 C omega ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w))
        ((Q:ℂ)^(-6*z)) scalar e l k m := by
  unfold sourceWeightedScalar weightedScalar
  rw [spectral_power_split Q hQ, cpow_half_eq_sqrt Q hQ.le]
  rw [zpow_neg, zpow_natCast]
  have hphase := source_signed_phase 1 omega ho e l k
  simp only [localCubePhase, one_pow, one_mul] at hphase
  unfold localCubePhase
  rw [hphase, mul_pow a C, hG]
  simp only [mul_pow, div_pow]

  ring

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma firstGauss_eq_gamma_sqrt (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda ∉ Ideal.span {p}) :
    primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 =
      localGamma p hp.ne_zero hg 1 *
        (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hs : (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hQ).ne'
  unfold localGamma
  rw [pow_one, ProbePhase.normalizedTraceGauss_eq_normalizedGauss]
  simp only [ProbeGauss.normalizedGauss, ← Nat.card_eq_fintype_card]
  change _ = (gaussSum _ _ / (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ)) * _
  rw [div_mul_cancel₀ _ hs]
  simp only [primeGauss, map_one, one_mul, tsum_fintype, gaussSum]

theorem sourceWeightedScalar_actual (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda ∉ Ideal.span {p})
    (eta a x w z scalar : ℂ) (e l k m : ℕ) :
    sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
      (actualSextic (Ideal.span {p}) hg (-1)) x w z scalar e l k m =
    weightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-6*z)) scalar e l k m := by
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  simpa only [Complex.ofReal_natCast] using
    sourceWeightedScalar_eq _ hQ eta a (localGamma p hp.ne_zero hg 1) _
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1))
      x w z scalar (firstGauss_eq_gamma_sqrt p hp hg)
      (actualSextic_neg_one_sq _ hg) e l k m

end SevenEighths.ProbeEuler
end

end OAI

end Source1029

/- Original source: OAI/NumberTheory/DirichletL/Detector/ZeroIndex.lean; sha256: 49f1b9219781ee95156776336245092a7486c916e4cad1cffdaebceac1530c70 -/
section Source1030
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]

def zeroIndexTerm (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) (k m : ℕ) : ℂ :=
  (if k=0 then 1 else (χ^k) (Ideal.Quotient.mk _ (p^(6*m)))) * W^k * V^m

omit [(Ideal.span {p}).IsMaximal] in
lemma zeroIndex_inner_zero (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (hV : ‖V‖<1) :
    HasSum (fun m => zeroIndexTerm p χ W V 0 m) (1/(1-V)) := by
  simpa [zeroIndexTerm, one_div] using hasSum_geometric_of_norm_lt_one hV

include hp in
lemma zeroIndex_inner_pos (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (k : ℕ) (hk : k≠0) :
    HasSum (fun m => zeroIndexTerm p χ W V k m) (W^k) := by
  apply (hasSum_ite_eq 0 (W^k)).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hm
  dsimp only
  unfold zeroIndexTerm
  rw [ite_eq_right hk, zero_index_scalar p hp χ k (6*m) hk]
  by_cases h : m=0
  · subst m; simp
  · have h6 : 6*m≠0 := by omega
    simp [h, h6]

def zeroIndexSeries (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) : ℂ :=
  ∑' k, ∑' m, zeroIndexTerm p χ W V k m

include hp in
lemma zeroIndexSeries_eq (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (hW : ‖W‖<1) (hV : ‖V‖<1) :
    zeroIndexSeries p χ W V = 1/(1-V)+W/(1-W) := by
  have htail : HasSum (fun k => ∑' m, zeroIndexTerm p χ W V (k+1) m) (W/(1-W)) := by
    have he : (fun k => ∑' m, zeroIndexTerm p χ W V (k+1) m) =
        (fun k => W * W^k) := by
      funext k
      rw [(zeroIndex_inner_pos p hp χ W V (k+1) (by omega)).tsum_eq, pow_succ]
      ring
    rw [he]
    simpa [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hW).mul_left W
  have hall := HasSum.sum_range_add (f := fun k => ∑' m, zeroIndexTerm p χ W V k m) (k := 1) htail
  simpa only [zeroIndexSeries, Finset.sum_range_one,
    (zeroIndex_inner_zero p χ W V hV).tsum_eq] using hall.tsum_eq

end SevenEighths.ProbeEuler
end

end OAI

end Source1030

/- Original source: OAI/NumberTheory/DirichletL/Detector/SourceLocal.lean; sha256: db29a85fc6d3e1c38ce9e8dce9e0f795baa68aa85b9a228c70df9991e0ec54c2 -/
section Source1031
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def sourceScalar (t k j : ℕ) : ℂ :=
  if t=0 then
    if k=0 then 1 else (actualSextic (Ideal.span {p}) hg ^ k) (Ideal.Quotient.mk _ (p^j))
  else positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (t-1) k j

def sourcePrincipalTerm (eta a x w z : ℂ) (e l k m : ℕ) : ℂ :=
  sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
    (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) x w z
    (sourceScalar p hp hg (e+3*l) k (6*m)) e l k m

lemma sourcePrincipalTerm_pos (eta a x w z : ℂ) (e l k m : ℕ) (ht : e+3*l≠0) :
    sourcePrincipalTerm p hp hg eta a x w z e l k m =
      principalMarkedTerm p hp hg eta a
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) e l k m := by
  unfold sourcePrincipalTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [sourceScalar, ht, ite_false, principalMarkedTerm, coordV, Complex.ofReal_natCast]

lemma sourcePrincipalTerm_zero (eta a x w z : ℂ) (k m : ℕ) :
    sourcePrincipalTerm p hp hg eta a x w z 0 0 k m =
      zeroIndexTerm p (actualSextic (Ideal.span {p}) hg)
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) k m := by
  unfold sourcePrincipalTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [weightedScalar, localCubePhase, sourceScalar, zeroIndexTerm, coordV,
    mul_zero, add_zero, pow_zero,  one_mul, zero_mul, Nat.choose_zero_succ,
    ite_true, Complex.ofReal_natCast]

def sourcePrincipalSeries (eta a x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m, sourcePrincipalTerm p hp hg eta a x w z e.val l k m

include hc in
lemma sourcePrincipalSeries_eq (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    sourcePrincipalSeries p hp hg eta a x w z =
      principalFullSeries p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) := by
  dsimp only
  simp only [Complex.ofReal_natCast]
  let X : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)
  let W : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)
  let V : ℂ := coordV (Ideal.absNorm (Ideal.span {p})) z
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hr : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1 := by
    have he := evenRatio_eq_coordR _ hQ a x z
    simp only [Complex.ofReal_natCast] at he
    change ‖evenRatio _ a _ _‖<1
    rw [he]
    exact hR
  have hW' : ‖W‖<1 := by simpa only [W, coordW, one_mul, Complex.ofReal_natCast] using hW
  have he : Summable (fun l => principalInner p hp hg eta a X W V 0 l) :=
    (principalInner_even_hasSum p hp hg hc eta a X W V hV hr).summable
  have h0 : (fun l => ∑' k, ∑' m, sourcePrincipalTerm p hp hg eta a x w z 0 l k m) =
      (fun l => principalInner p hp hg eta a X W V 0 l +
        if l=0 then zeroIndexSeries p (actualSextic (Ideal.span {p}) hg) W V else 0) := by
    funext l
    by_cases hl : l=0
    · subst l
      simp only [sourcePrincipalTerm_zero, principalInner_zero p hp hg,  ite_true,
        zero_add, zeroIndexSeries, W, V]
    · rw [ite_eq_right hl, add_zero]
      apply tsum_congr
      intro k
      apply tsum_congr
      intro m
      exact sourcePrincipalTerm_pos p hp hg eta a x w z 0 l k m (by omega)
  have h1 : (fun l => ∑' k, ∑' m, sourcePrincipalTerm p hp hg eta a x w z 1 l k m) =
      (fun l => principalInner p hp hg eta a X W V 1 l) := by
    funext l
    apply tsum_congr
    intro k
    apply tsum_congr
    intro m
    exact sourcePrincipalTerm_pos p hp hg eta a x w z 1 l k m (by omega)
  unfold sourcePrincipalSeries principalFullSeries principalMarkedSeries
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [h0, h1, he.tsum_add (hasSum_ite_eq 0 _).summable, tsum_ite_eq]
  rw [zeroIndexSeries_eq p hp _ W V hW' hV]
  change _ = 1/(1-V)+W/(1-W)+((∑' l, principalInner p hp hg eta a X W V 0 l)+
    ∑' l, principalInner p hp hg eta a X W V 1 l)
  ring

include hc in

theorem sourcePrincipalSeries_euler_identity (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta 1 x ≠ 0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    sourcePrincipalSeries p hp hg eta a x w z =
      (1-coordD Q eta 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q (a^2) eta 1 x w z := by
  rw [sourcePrincipalSeries_eq p hp hg hc eta a x w z hV hR hW]
  exact principalFullSeries_euler_identity p hp hg hc eta a x w z hV hR hW hD

end SevenEighths.ProbeEuler
end

end OAI

end Source1031

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalLocalEuler.lean; sha256: 59744e9d65c34d8209cc52288edac81e8b6fdd07bfe1b598ffc19943d8b9eca6 -/
section Source1032
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion
open CubicEisenstein GaussianShiftedPartition ProbePrimePower ProbeEuler ProbeLocal
local notation "O" => ActualEisensteinCubic.O

lemma outerQuotient_mk (s H : O) :
    outerQuotient s (Ideal.Quotient.mk _ H)=idealRowHom H (Ideal.span {s}) := by
  unfold outerQuotient
  apply idealRowHom_congr_mod
  exact Ideal.Quotient.eq.mp (representative_spec _ _)

theorem bareCongruenceCoefficient_all_prime_powers (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      sourceScalar p hp hg t k j := by
  cases t with
  | zero =>
    simp only [pow_zero]
    rw [bareCongruenceCoefficient_inner_one _ (pow_ne_zero _ hp.ne_zero), outerQuotient_mk]
    unfold sourceScalar
    rw [ite_eq_left rfl]
    by_cases hk : k=0
    · subst k
      simp only [pow_zero, Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one, ite_true]
    · rw [ite_eq_right hk, ← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg,
        MulChar.pow_apply' _ hk]
  | succ n =>
    rw [bareCongruenceCoefficient_prime_power p hp hg n k j]
    simp only [sourceScalar, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel]

def physicalPrincipalSeries (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (eta a x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m,
    sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
      (actualSextic (Ideal.span {p}) hg (-1)) x w z
      (bareCongruenceCoefficient (p^(e.val+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^(6*m)))
      e.val l k m

theorem physicalPrincipalSeries_eq (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (eta a x w z : ℂ) :
    physicalPrincipalSeries p hp hg eta a x w z = sourcePrincipalSeries p hp hg eta a x w z := by
  simp only [physicalPrincipalSeries, sourcePrincipalSeries, sourcePrincipalTerm,
    bareCongruenceCoefficient_all_prime_powers p hp hg]

theorem physicalPrincipalSeries_euler_identity (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta 1 x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    physicalPrincipalSeries p hp hg eta a x w z =
      (1-coordD Q eta 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q (a^2) eta 1 x w z := by
  rw [physicalPrincipalSeries_eq]
  exact sourcePrincipalSeries_euler_identity p hp hg hc eta a x w z hV hR hW hD

end SevenEighths.ProbePhysical
end

end OAI

end Source1032

/- Original source: OAI/NumberTheory/DirichletL/Detector/LocalUnitFrequency.lean; sha256: e9ff5a6c85d1f956dd9f53409637e72f229be1d6fc3c7b97f2cb2ff931b4a387 -/
section Source1033
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
open CompletedGauss ConcreteTraceCRT GaussianShiftedPartition CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation ConcretePrimeRowBridge ProbePrimePower ProbeLocal ProbeEuler
local notation "O" => ActualEisensteinCubic.O

lemma finite_fourier_unit_scale {R : Type*} [CommRing R] [Fintype R]
    (F : R → ℂ) (ψ : AddChar R ℂ) (u : Rˣ) (c : ℂ) (hc : c ≠ 0)
    (hF : ∀ x, F ((u : R) * x) = c * F x) (H : R) :
    (∑ x, F x * ψ (((u : R) * H) * x)) = c⁻¹ * ∑ x, F x * ψ (H*x) := by
  have he : (∑ x, F x * ψ (H*x)) = c * ∑ x, F x * ψ (((u : R)*H)*x) := by
    rw [← Equiv.sum_comp u.mulLeft (fun x => F x * ψ (H*x))]
    simp only [Units.mulLeft_apply, hF, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show H*((u : R)*x) = ((u : R)*H)*x by ring]
    ring
  rw [he, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem barePhysicalFourier_unit_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    barePhysicalFourier A s (supportedElement_ne_zero A hA)
        (supportedElement_ne_zero s hs) (b*H) =
      ((idealRowHom b (Ideal.span {A}))⁻¹ * idealRowHom b (Ideal.span {s})) *
        barePhysicalFourier A s (supportedElement_ne_zero A hA)
          (supportedElement_ne_zero s hs) H := by
  have hAs := mul_ne_zero (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs)
  let := finite_quotient_span hAs
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let u := residueUnit (A*s) b hcop.symm
  have hcA := idealRowHom_ne_zero_of_coprime A b hA hcop.of_mul_right_left.symm
  have hcs := idealRowHom_ne_zero_of_coprime s b hs hcop.of_mul_right_right.symm
  have hF (x : Residue (A*s)) :
      movingQuotient A s (supportedElement_ne_zero s hs) ((u : Residue (A*s))*x) =
        (idealRowHom b (Ideal.span {A}) * (idealRowHom b (Ideal.span {s}))⁻¹) *
          movingQuotient A s (supportedElement_ne_zero s hs) x := by
    exact movingQuotient_unit_scale A s hs b hcop.of_mul_right_right x
  have he := finite_fourier_unit_scale (movingQuotient A s (supportedElement_ne_zero s hs))
    (quotientTrace (A*s) hAs) u _ (mul_ne_zero hcA (inv_ne_zero hcs)) hF
    (Ideal.Quotient.mk _ H)
  unfold barePhysicalFourier elementFourier
  simp only [tsum_fintype]
  change (∑ x, movingQuotient A s (supportedElement_ne_zero s hs) x *
    quotientTrace (A*s) hAs (Ideal.Quotient.mk _ (b*H)*x)) =
      _ * ∑ x, movingQuotient A s (supportedElement_ne_zero s hs) x *
        quotientTrace (A*s) hAs (Ideal.Quotient.mk _ H*x)
  simpa only [u, residueUnit_coe, map_mul, mul_inv_rev, inv_inv, mul_comm] using he

theorem bareCongruenceCoefficient_unit_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (b*H) =
      ((idealRowHom b (Ideal.span {A}))⁻¹ * idealRowHom b (Ideal.span {s})) *
        bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H := by
  have he := barePhysicalFourier_unit_frequency A s hA hs b H hcop
  simp only [barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  apply mul_left_cancel₀ hn
  rw [he]
  ring

lemma idealRowHom_norm_one_of_coprime (s b : O)
    (hs : Supported (Ideal.span {s})) (hcop : IsCoprime b s) :
    ‖idealRowHom b (Ideal.span {s})‖ = 1 := by
  have h6 := idealRowHom_sixth_mask b (Ideal.span {s}) hs
  rw [idealRowHom_argument_pow _ _ _ hs,
    ite_eq_left ((Ideal.isCoprime_span_singleton_iff s b).mpr hcop.symm)] at h6
  exact Complex.norm_eq_one_of_pow_eq_one h6 (by decide : (6 : ℕ) ≠ 0)

theorem bareCongruenceCoefficient_unit_frequency_norm (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (b*H)‖ =
      ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ := by
  rw [bareCongruenceCoefficient_unit_frequency A s hA hs b H hcop,
    norm_mul, norm_mul, norm_inv,
    idealRowHom_norm_one_of_coprime A b hA hcop.of_mul_right_left,
    idealRowHom_norm_one_of_coprime s b hs hcop.of_mul_right_right,
    inv_one, one_mul, one_mul]

theorem bareCongruenceCoefficient_unit_frequency_eq_zero_iff (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (b*H) = 0 ↔
      bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H = 0 := by
  rw [← norm_eq_zero, bareCongruenceCoefficient_unit_frequency_norm A s hA hs b H hcop,
    norm_eq_zero]

lemma supported_element_power (p : O) (hs : Supported (Ideal.span {p})) (n : ℕ) :
    Supported (Ideal.span {p^n}) := by
  rw [← Ideal.span_singleton_pow]
  exact supported_pow hs n

lemma idealRowHom_prime_power_value (p b : O) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (n : ℕ) :
    idealRowHom b (Ideal.span {p^n}) =
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^n := by
  rw [← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg]

lemma actualSextic_unit_power_ne_zero (p b : O) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hcop : IsCoprime b p) (t : ℕ) :
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t ≠ 0 := by
  apply pow_ne_zero
  exact (actualSextic (Ideal.span {p}) hg).apply_ne_zero_iff.mpr
    ((isUnit_quotient_span_iff p b).mpr hcop.symm)

theorem bareCongruenceCoefficient_prime_power_unit_frequency (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      ((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
          bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) := by
  have he := bareCongruenceCoefficient_unit_frequency (p^t) (p^k)
    (supported_element_power p hs t) (supported_element_power p hs k) b (p^j)
    (hcop.pow_right.mul_right hcop.pow_right)
  simpa only [idealRowHom_prime_power_value p b hg, div_eq_mul_inv, mul_comm] using he

theorem bareCongruenceCoefficient_all_prime_powers_unit (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      ((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
          sourceScalar p hp hg t k j := by
  rw [bareCongruenceCoefficient_prime_power_unit_frequency p hp hs hg b hcop t k j,
    bareCongruenceCoefficient_all_prime_powers p hp hg t k j]

theorem barePhysicalFourier_all_prime_powers_unit (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    barePhysicalFourier (p^t) (p^k) (pow_ne_zero _ hp.ne_zero)
        (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      (Ideal.absNorm (Ideal.span {p^k}) : ℂ) *
        (((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
          (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
            sourceScalar p hp hg t k j) := by
  rw [barePhysicalFourier_eq,
    bareCongruenceCoefficient_all_prime_powers_unit p hp hs hg b hcop t k j]

theorem bareCongruenceCoefficient_all_prime_powers_unit_norm (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    ‖bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j)‖ =
      ‖sourceScalar p hp hg t k j‖ := by
  have he := bareCongruenceCoefficient_unit_frequency_norm (p^t) (p^k)
    (supported_element_power p hs t) (supported_element_power p hs k) b (p^j)
    (hcop.pow_right.mul_right hcop.pow_right)
  rw [bareCongruenceCoefficient_all_prime_powers p hp hg t k j] at he
  exact he

end SevenEighths.ProbePhysical
end

end OAI

end Source1033

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsWeights.lean; sha256: 37a16ed08bc8531d0ee015d67c95dfcdf1c9995557d952daa50051929518a96c -/
section Source1034
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma localCubePhase_step_two (C omega : ℂ) (hC : C^2=omega) (ho : omega^2=1)
    (e l k : ℕ) : localCubePhase C omega e (l+2) k=localCubePhase C omega e l k := by
  have hchoose : (l+2).choose 2=l.choose 2+2*l+1 := by
    rw [show l+2=(l+1)+1 by omega,Nat.choose_succ_succ,Nat.choose_one_right,
      Nat.choose_succ_succ,Nat.choose_one_right]
    change l+1+(l+l.choose 2)=l.choose 2+2*l+1
    omega
  unfold localCubePhase
  rw [pow_add C l 2,hC,hchoose]
  have he : (e+3*(l+2))*k+e*(l+2)+(l.choose 2+2*l+1)=
      ((e+3*l)*k+e*l+l.choose 2)+(2*(3*k+e+l)+1) := by ring
  have ht : omega^(2*(3*k+e+l)+1)=omega := by
    rw [pow_add,pow_mul omega 2,ho,one_pow,pow_one,one_mul]
  rw [he,pow_add omega _ (2*(3*k+e+l)+1),ht]
  calc
    _ = C^l*omega^((e+3*l)*k+e*l+l.choose 2)*omega^2 := by ring
    _ = _ := by rw [ho,mul_one]

theorem weightedScalar_step_two (Q eta a G1 C omega X W V scalar : ℂ)
    (hQ : Q≠0) (hC : C^2=omega) (ho : omega^2=1) (e l k m : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^6*scalar) e (l+2) k (m+1)=
      evenRatio Q a X V*weightedScalar Q eta a G1 C omega X W V scalar e l k m := by
  unfold weightedScalar evenRatio
  rw [localCubePhase_step_two C omega hC ho]
  rw [pow_add (a*X^3/Q) l 2,pow_succ V m]
  have hbase : (a*X^3/Q)^2*Q^6=a^2*Q^4*X^6 := by
    field_simp
  linear_combination (-eta*X/G1)^e*(a*X^3/Q)^l*localCubePhase C omega e l k*scalar*W^k*V^m*V*hbase

def rowWeightedScalar (Q eta a G1 C omega X W V rho scalar : ℂ) (e l k m : ℕ) : ℂ :=
  (rho^k/rho^(e+3*l))*weightedScalar Q eta a G1 C omega X W V scalar e l k m

lemma rowWeightedScalar_zero (Q eta a G1 C omega X W V rho : ℂ) (e l k m : ℕ) :
    rowWeightedScalar Q eta a G1 C omega X W V rho 0 e l k m=0 := by
  rw [rowWeightedScalar,weightedScalar_zero,mul_zero]

theorem rowWeightedScalar_parameters (Q eta a G1 C omega X W V rho scalar : ℂ)
    (e l k m : ℕ) :
    rowWeightedScalar Q eta a G1 C omega X W V rho scalar e l k m=
      weightedScalar Q (eta/rho) (a/rho^3) G1 C omega X (rho*W) V scalar e l k m := by
  unfold rowWeightedScalar weightedScalar
  simp only [pow_add,pow_mul,mul_pow,div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

theorem evenRatio_unit (Q a X V rho : ℂ) (hρ : rho^6=1) :
    evenRatio Q (a/rho^3) X V=evenRatio Q a X V := by
  unfold evenRatio
  rw [div_pow,←pow_mul,show 3*2=6 by decide,hρ,div_one]

theorem rowWeightedScalar_step_two (Q eta a G1 C omega X W V rho scalar : ℂ)
    (hQ : Q≠0) (hC : C^2=omega) (ho : omega^2=1) (hρ : rho^6=1) (e l k m : ℕ) :
    rowWeightedScalar Q eta a G1 C omega X W V rho (Q^6*scalar) e (l+2) k (m+1)=
      evenRatio Q a X V*rowWeightedScalar Q eta a G1 C omega X W V rho scalar e l k m := by
  rw [rowWeightedScalar_parameters,rowWeightedScalar_parameters,
    weightedScalar_step_two Q (eta/rho) (a/rho^3) G1 C omega X (rho*W) V scalar hQ hC ho,
    evenRatio_unit Q a X V rho hρ]

end SevenEighths.ProbeEuler
end

end OAI

end Source1034

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsScalar.lean; sha256: 23c105eaef16417353ac64fdc414716ab0da6d28fde63eeaee7deed646093cdb -/
section Source1035
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
include hc

theorem row_even_kzero (r m j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+5) 0 (j+6*m) =
      if r+1≤m then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5)*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else if j=5 ∧ m=r then -(Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) else 0 := by
  rw [positiveScalar_kzero,actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_left (by omega : 6∣6*r+5+1)]
  by_cases hm : r+1≤m
  · rw [ite_eq_left hm,ite_eq_left (by omega),ite_eq_left (by omega),pow_succ]
    ring
  · rw [ite_eq_right hm,ite_eq_right (by omega)]
    by_cases hb : j=5 ∧ m=r
    · rw [ite_eq_left hb,ite_eq_left (by omega),zero_sub]
    · rw [ite_eq_right hb,ite_eq_right (by omega),sub_self]

theorem row_nonprincipal_kzero (r m j d : ℕ) (hj : j<6) (hd : d<5) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+d) 0 (j+6*m) =
      if j=d ∧ m=r then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+d)*
          primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^(d+1)) 1
      else 0 := by
  rw [positiveScalar_kzero,actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_right (by omega : ¬6∣6*r+d+1)]
  rw [show 6*r+d+1=6*r+(d+1) by omega,actualSextic_pow_six_mul_add _ hg hc]
  have he : j+6*m=6*r+d ↔ j=d ∧ m=r := by omega
  simp only [he]

theorem row_squarefree_kone (r m j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r) 1 (j+6*m) =
      ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1) *
        (if 6*r+1<j+6*m then
          (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r)*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
        else if j=1 ∧ m=r then -(Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) else 0) := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by decide : (1:ℕ)≠0)]
  by_cases hpos : 1≤j+6*m
  · rw [ite_eq_left ⟨rfl,hpos⟩,gaussValuationTable,ite_eq_left (by omega : 6∣6*r)]
    congr 1
    by_cases hb : 6*r+1<j+6*m
    · rw [ite_eq_left hb,ite_eq_left (by omega),ite_eq_left (by omega),pow_succ]
      ring
    · rw [ite_eq_right hb,ite_eq_right (by omega)]
      by_cases he : j=1 ∧ m=r
      · rw [ite_eq_left he,ite_eq_left (by omega),zero_sub]
      · rw [ite_eq_right he,ite_eq_right (by omega),sub_self]
  · rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),mul_zero]

theorem row_nonprincipal_kone (r m j d : ℕ) (hj : j<6) (hd0 : 0<d) (hd : d<5) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+d) 1 (j+6*m) =
      if j=d+1 ∧ m=r then
        ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
          primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1) *
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+d)*
            primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^d) 1)
      else 0 := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by decide : (1:ℕ)≠0)]
  by_cases hpos : 1≤j+6*m
  · rw [ite_eq_left ⟨rfl,hpos⟩,gaussValuationTable,ite_eq_right (by omega : ¬6∣6*r+d),
      actualSextic_pow_six_mul_add _ hg hc]
    by_cases he : j=d+1 ∧ m=r
    · rw [ite_eq_left he,ite_eq_left (by omega)]
    · rw [ite_eq_right he,ite_eq_right (by omega),mul_zero]
  · rw [ite_eq_right (by omega),ite_eq_right (by omega)]

end SevenEighths.ProbePrimePower
end

end OAI

end Source1035

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsRecurrence.lean; sha256: 902553f80818893429286c2aba1b8bd9c2fd2a25b82d98655ef4c52cda5003b6 -/
section Source1036
namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma gaussValuationTable_step_six (Q G : ℂ) (r n j : ℕ) :
    gaussValuationTable Q G (r+6) (n+6) (j+6)=Q^6*gaussValuationTable Q G r n j := by
  have hd : 6∣r+6 ↔ 6∣r := by omega
  have hle : n+6+1≤j+6 ↔ n+1≤j := by omega
  have hle' : n+6≤j+6 ↔ n≤j := by omega
  have he : j+6=n+6 ↔ j=n := by omega
  simp only [gaussValuationTable,hd,hle,hle',he]
  split_ifs <;> simp [pow_add] <;> ring

theorem positiveScalar_step_six (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k j : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (n+6) k (j+6)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^6*
        positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  rw [positiveScalar_actual_table p hp hg hc,positiveScalar_actual_table p hp hg hc]
  have hp6 (a : ℕ) : actualSextic (Ideal.span {p}) hg^(a+6)=
      actualSextic (Ideal.span {p}) hg^a := by
    rw [pow_add,actualSextic_six _ hg hc,mul_one]
  by_cases hk : k=0
  · simp only [hk,ite_true]
    rw [show n+6+1=(n+1)+6 by omega,hp6,gaussValuationTable_step_six]
  · simp only [ite_eq_right hk]
    by_cases hk1 : k=1
    · subst k
      by_cases hj : 1≤j
      · rw [ite_eq_left ⟨rfl,by omega⟩,ite_eq_left ⟨rfl,hj⟩,hp6,
          show j+6-1=(j-1)+6 by omega,gaussValuationTable_step_six]
        ring
      · have hz : j=0 := by omega
        subst j
        simp only [show (1:ℕ)≤0+6 by omega,show ¬(1:ℕ)≤0 by omega,
          and_true,and_false,ite_true,ite_false,mul_zero]
        simp only [gaussValuationTable]
        split_ifs <;> simp_all ; omega
    · rw [ite_eq_right (by omega),ite_eq_right (by omega),mul_zero]

theorem positiveScalar_zero_below (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k j : ℕ) (hj : j<n) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j=0 := by
  rw [positiveScalar_actual_table p hp hg hc]
  split_ifs with hk hk1
  · simp only [gaussValuationTable]
    split_ifs <;> simp_all <;> omega
  · have hbelow : j-1<n := by omega
    have hz : gaussValuationTable (Ideal.absNorm (Ideal.span {p}))
        (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^n) 1) n n (j-1)=0 := by
      simp only [gaussValuationTable]
      split_ifs <;> simp_all <;> omega
    rw [hz,mul_zero]
  · rfl

end SevenEighths.ProbePrimePower
end

end OAI

end Source1036

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsSeries.lean; sha256: e5c7b7e35821cf05b5c656e9cb61729aeadb154fe866402db593ef3524b50a2a -/
section Source1037
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def rowMarkedTerm (eta a X W V rho : ℂ) (j e l k m : ℕ) : ℂ :=
  if e+3*l=0 then 0 else
    rowWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1)) X W V rho
      (positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (e+3*l-1) k (j+6*m)) e l k m

include hc in
theorem rowMarkedTerm_step (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (j e l k m : ℕ) (ht : 0<e+3*l) :
    rowMarkedTerm p hp hg eta a X W V rho j e (l+2) k (m+1)=
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
        rowMarkedTerm p hp hg eta a X W V rho j e l k m := by
  unfold rowMarkedTerm
  rw [ite_eq_right (by omega),ite_eq_right (by omega),
    show e+3*(l+2)-1=(e+3*l-1)+6 by omega,
    show j+6*(m+1)=(j+6*m)+6 by omega,
    positiveScalar_step_six p hp hg hc]
  exact rowWeightedScalar_step_two _ _ _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (localGamma_conjugate_three_sq p hp hg hc) (actualSextic_neg_one_sq _ hg) hρ e l k m

theorem rowMarkedTerm_higher_outer (eta a X W V rho : ℂ) (j e l k m : ℕ) :
    rowMarkedTerm p hp hg eta a X W V rho j e l (k+2) m=0 := by
  unfold rowMarkedTerm
  split_ifs
  · rfl
  · rw [positiveScalar_kge_two p hp,rowWeightedScalar_zero]

end SevenEighths.ProbeEuler
end

end OAI

end Source1037

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/GaussNorm.lean; sha256: 291a73b249f3d1944a963edd7162a1d5617d55b9b180cf49c21eee5332cdb5a8 -/
section Source1038
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma primeIndex_product (I : Ideal O) (hI : Admissible I) :
    (∏ P : PrimeIndex I, P.val) = I := by
  have hI0 := primaryGenerator_ne_zero_ideal I hI.2
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hI.1
  have hv : (CompletedGauss.primeSupport I).val = UniqueFactorizationMonoid.normalizedFactors I := by
    simpa only [CompletedGauss.primeSupport, Multiset.toFinset_val] using hnodup.dedup
  calc
    _ = ∏ P ∈ CompletedGauss.primeSupport I, P := Finset.prod_coe_sort _ _
    _ = (CompletedGauss.primeSupport I).val.prod := (Finset.prod_val _).symm
    _ = I := by rw [hv]; exact Ideal.prod_normalizedFactors_eq_self hI0

theorem gaussTwo_norm_one (I : Ideal O) (hI : Admissible I) : ‖gaussTwo I hI.2‖ = 1 := by
  let c := primaryGenerator I
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hI.2
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (P : PrimeIndex I) : Fintype (O ⧸ P.val) := Fintype.ofFinite _
  let (P : PrimeIndex I) : Field (O ⧸ P.val) := Ideal.Quotient.field P.val
  have hc : Ideal.span {c} = ∏ P : PrimeIndex I, P.val :=
    (primaryGenerator_spec I hI.2).1.trans (primeIndex_product I hI).symm
  let e : (O ⧸ Ideal.span {c}) ≃+* ∀ P : PrimeIndex I, O ⧸ P.val :=
    (Ideal.quotEquivOfEq hc).trans
      (IdealGaussCRT.quotientProdEquivPi (fun P : PrimeIndex I => P.val)
        (CanonicalRowCompletion.primeIndex_pairwise_coprime I))
  let χ : ∀ P : PrimeIndex I, MulChar (O ⧸ P.val) ℂ :=
    fun P => actualSextic P.val (primeIndex_good I hI.2 P) ^ 2
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hI.2
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hI.2
  have hχ : ∀ P : PrimeIndex I, χ P ≠ 1 := fun P =>
    cubicExponent_nonprincipal P.val (primeIndex_good I hI.2 P) false
  have hnormsq := IdealGaussCRT.norm_gauss_finite_crt_sq (fun P : PrimeIndex I => O ⧸ P.val)
    e χ ψ hχ (fun P => IdealGaussCRT.coordinateAddChar_isPrimitive
      (fun P : PrimeIndex I => O ⧸ P.val) e ψ hψ P)
  have hrow (x : O ⧸ Ideal.span {c}) : (∏ P : PrimeIndex I, χ P (e x P)) =
      CompletedGauss.cubicRow I hI.2 ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) x) := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    dsimp only [c] at z ⊢
    simp only [e, c, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      IdealGaussCRT.quotientProdEquivPi_mk, CompletedGauss.cubicRow_mk, χ]
  simp_rw [hrow] at hnormsq
  have hcard : (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = ‖eisEmbedding c‖ ^ 2 := by
    symm
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] using
      eisEmbedding_norm_sq_eq_absNorm_span c
  rw [hcard] at hnormsq
  have hnorm := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq
  change ‖(∑ x : O ⧸ Ideal.span {c},
    CompletedGauss.cubicRow I hI.2 ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) x) * ψ x) /
    (‖eisEmbedding c‖ : ℂ)‖ = 1
  rw [norm_div, hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hI.2))

end
end SevenEighths.CubicSieve

end OAI

end Source1038

/- Original source: OAI/NumberTheory/DirichletL/Detector/SourceBounds.lean; sha256: 86184dc0cca58d1494ee7cdb68149db84b16182995d0007d29b9ca6b7759428c -/
section Source1039
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbePhase ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem bareCongruenceCoefficient_norm_le (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    ‖bareCongruenceCoefficient A s hA H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  apply congruenceCoefficient_norm_le A s hA hs
  · intro m
    exact idealRowHom_norm _ _
  · intro m
    exact idealRowHom_norm _ _

theorem bareSourceCoefficient_norm_le (η : HeckeFamily.Character)
    (I : Ideal O) (hI : CubicSieve.Admissible I) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s})) (H : O) :
    ‖bareSourceCoefficient η I hI.2 A s (supportedElement_ne_zero A hA) H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  have hR : ‖reciprocitySign A s‖≤1 := sexticReciprocityPhase_norm A s
  have ht := targetMonoid_norm_le_one η A
  have hfac : ‖targetMonoid η A‖*‖reciprocitySign A s‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) ht).trans hR
  calc
    _ = (‖targetMonoid η A‖*‖reciprocitySign A s‖)*
        ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ := by
      simp only [bareSourceCoefficient, correctedFiniteCoefficient, reciprocityCoefficient,
        norm_mul,norm_star,CubicSieve.gaussTwo_norm_one I hI,
        FiniteGaussPhase.norm_angularFactor A (supportedElement_ne_zero A hA),
        G_norm_one_of_odd A (supported_residue_odd A hA),one_mul,mul_one]
      ring
    _ ≤ ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hfac
    _ ≤ _ := bareCongruenceCoefficient_norm_le A s (supportedElement_ne_zero A hA)
      (supportedElement_ne_zero s hs) H

end SevenEighths.ProbePhysical
end

end OAI

end Source1039
