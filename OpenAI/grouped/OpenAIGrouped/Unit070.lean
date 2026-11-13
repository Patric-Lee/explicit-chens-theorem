import OpenAIGrouped.Unit058
import OpenAIGrouped.Unit069
import OpenAIGrouped.Unit059
import OpenAIGrouped.Unit063
import OpenAIGrouped.Unit040
import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit018
import OpenAIGrouped.Unit013
import OpenAIGrouped.Unit025
import OpenAIGrouped.Unit033
import OpenAIGrouped.Unit060
import OpenAIGrouped.Unit015
import OpenAIGrouped.Unit008
import OpenAIGrouped.Unit012

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialRetainedSupport.lean; sha256: ee9f53d0c5774535e1f95261cc2c5ffacddda6db2bddfed0ac4dd6604a4de083 -/
section Source2800
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialRetainedSupport
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT CompletedGauss
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialKernelBridge SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,goodLambda∉Ideal.span {p i})

theorem live_cutoffs (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m:ℝ)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    W₁ (coordinates p x 0*coordinates p x 2*coordinates p x 4/Z^D)≠0 ∧
    W₂ (coordinates p x 0*coordinates p x 2*coordinates p x 5/Z^D)≠0 := by
  rw [physicalTerm_extracted p hp hcop hg hpr Ψ j σ W₁ W₂ Φ Z D m x hx ρ] at hne
  have hk:= (mul_ne_zero_iff.mp hne).2
  unfold physicalKernel at hk
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hk).1).1).2,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hk).1).2⟩

theorem live_whole_columns (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m b:ℝ)(hZ:0<Z)(hs₁:Function.support W₁⊆Set.Iic b)
    (hs₂:Function.support W₂⊆Set.Iic b)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    coordinates p x 0*coordinates p x 2*coordinates p x 4≤b*Z^D ∧
    coordinates p x 0*coordinates p x 2*coordinates p x 5≤b*Z^D := by
  obtain ⟨h₁,h₂⟩:=live_cutoffs p hp hcop hg hpr Ψ j σ W₁ W₂ Φ Z D m x hx ρ hne
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ D)).mp (hs₁ h₁),
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ D)).mp (hs₂ h₂)⟩

include hp in
omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
theorem ideal_coordinates_one (x:Point ι):
    1≤coordinates p x 0 ∧ 1≤coordinates p x 1 ∧ 1≤coordinates p x 2 ∧
    1≤coordinates p x 4 ∧ 1≤coordinates p x 5 := by
  have hi (S:Finset ι):(1:ℝ)≤((sourceIdeal p S).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp S))
  exact ⟨hi _,hi _,hi _,hi _,hi _⟩

theorem live_ideal_caps (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m b:ℝ)(hZ:0<Z)(hs₁:Function.support W₁⊆Set.Iic b)
    (hs₂:Function.support W₂⊆Set.Iic b)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    coordinates p x 0≤b*Z^D ∧ coordinates p x 1≤b*Z^D ∧
    coordinates p x 2≤b*Z^D ∧ coordinates p x 4≤b*Z^D ∧
    coordinates p x 5≤b*Z^D := by
  obtain ⟨h₁,h₂⟩:=live_whole_columns p hp hcop hg hpr Ψ j σ W₁ W₂ Φ
    Z D m b hZ hs₁ hs₂ x hx ρ hne
  obtain ⟨hC,hd,hs,hn₁,hn₂⟩:=ideal_coordinates_one p hp x
  have hpair:1≤coordinates p x 0*coordinates p x 2:=by nlinarith
  have hcp:coordinates p x 0≤coordinates p x 0*coordinates p x 2:=
    le_mul_of_one_le_right (by linarith) hs
  have hsp:coordinates p x 2≤coordinates p x 0*coordinates p x 2:=
    le_mul_of_one_le_left (by linarith) hC
  have hbig:coordinates p x 0*coordinates p x 2≤b*Z^D:=
    (le_mul_of_one_le_right (by positivity) hn₁).trans h₁
  have hdiv:coordinates p x 1≤coordinates p x 0:=by
    change ((sourceIdeal p x.divisor).absNorm:ℝ)≤(sourceIdeal p x.common).absNorm
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _)))
      (map_dvd Ideal.absNorm (sourceIdeal_dvd p _ _ hx.divisor_subset))
  exact ⟨hcp.trans hbig,hdiv.trans (hcp.trans hbig),hsp.trans hbig,
    (le_mul_of_one_le_left (by linarith) hpair).trans h₁,
    (le_mul_of_one_le_left (by linarith) hpair).trans h₂⟩

end SevenEighths.InverseInitialRetainedSupport

end

end OAI

end Source2800

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialDyadicAssemblySourceCaps.lean; sha256: f8ed1099c8288c5eafe125a30381ab4193d7438b2a6af6eccf75e4581c638b45 -/
section Source2801
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseInitialKernelBridge InverseSecondChildWindows

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

omit [DecidableEq ι] in
theorem sourceNorms_fresh (x:Source (ι:=ι) 0)(N M:Finset ι)(i:Fin 4) :
    sourceNorms p x i=coordinates p (sourcePoint x N M) (outerIndex i) := by
  fin_cases i <;> simp only [sourceNorms,coordinates,sourcePoint,physicalCoordinates,
    outerIndex,Fin.castLE,Matrix.cons_val_zero',Matrix.cons_val_succ']

def physicalCaps (b Z D T:ℝ) : Fin 4→ℝ := ![b*Z^D,b*Z^D,b*Z^D,T]

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem actual_live_caps
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m b T:ℝ)(hZ:0<Z)
    (hW₁:Function.support W₁⊆Set.Iic b)(hW₂:Function.support W₂⊆Set.Iic b)
    (hT:∀x∈S,sourceNorms p x 3≤T)
    (x:Source (ι:=ι) 0)(hx:x∈S)(N:Finset ι)(hN:N∈(pool\x.overlap).powerset)
    (M:Finset ι)(hM:M∈(pool\x.overlap).powerset)(ρ:SecondRayIndex)
    (hn:w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m (sourcePoint x N M) ρ≠0) :
    ∀i,sourceNorms p x i∈Set.Icc 1 (physicalCaps b Z D T i) := by
  have hpnt:sourcePoint x N M∈pointSource pool S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,?_⟩
    exact Finset.mem_image.mpr ⟨(N,M),Finset.mem_product.mpr ⟨hN,hM⟩,rfl⟩
  have hv:=pointSource_valid pool S hdiv hf _ hpnt
  have hc:=InverseInitialRetainedSupport.live_ideal_caps p hp hcop hg hpr Ψ j marks W₁ W₂ Φ
    Z D m b hZ hW₁ hW₂ (sourcePoint x N M) hv ρ (mul_ne_zero_iff.mp hn).2
  intro i
  refine ⟨sourceNorms_one_le p hp x (hf x hx) i,?_⟩
  fin_cases i
  · change sourceNorms p x 0≤b*Z^D
    rw [sourceNorms_fresh p x N M 0]
    exact hc.1
  · change sourceNorms p x 1≤b*Z^D
    rw [sourceNorms_fresh p x N M 1]
    exact hc.2.1
  · change sourceNorms p x 2≤b*Z^D
    rw [sourceNorms_fresh p x N M 2]
    exact hc.2.2.1
  · exact hT x hx

theorem actual_physical_partition
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m b T:ℝ)(hZ:1<Z)
    (hW₁:Function.support W₁⊆Set.Iic b)(hW₂:Function.support W₂⊆Set.Iic b)
    (hT:∀x∈S,sourceNorms p x 3≤T) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows (fun _=>1) (physicalCaps b Z D T),
      windowBlock p hp hcop hg pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T))
        w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val) := by
  exact physicalBlock_live_partition p hp hcop hg pool S (fun _=>1) (physicalCaps b Z D T)
    (by intro i; norm_num) w Ψ j marks W₁ W₂ Φ Z D m hZ
    (actual_live_caps p hp hcop hg hpr pool S hdiv hf w Ψ j marks W₁ W₂ Φ Z D m b T
      (by linarith) hW₁ hW₂ hT)

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end Source2801

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialDyadicAssemblyWindows.lean; sha256: 5606fcd09caeed967d234216391b8cac1a3a7601184bc889715b4d10e457ac81 -/
section Source2802
namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff
namespace SevenEighths.InverseInitialDyadicAssembly
open CenteredMomentSectorLocalization CenteredMomentDyadicCount
open Filter

theorem cutoff_smooth (i:Fin 4) : ContDiff ℝ ∞ (cutoff i) :=
  Complex.ofRealCLM.contDiff.comp annulus_smooth

theorem cutoff_norm_le (i:Fin 4)(x:ℝ) : ‖cutoff i x‖≤1 := by
  simpa only [cutoff,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (annulus_bounds x).1] using (annulus_bounds x).2

theorem cutoff_support (i:Fin 4) :
    Function.support (cutoff i)⊆Set.Ioo (1/4:ℝ) 1 := by
  intro x hx
  have hn:annulus x≠0 := by simpa only [Function.mem_support,cutoff,ne_eq,Complex.ofReal_eq_zero] using hx
  exact ⟨lt_of_not_ge (fun h=>hn (annulus_zero_low x h)),
    lt_of_not_ge (fun h=>hn (annulus_zero_high x h))⟩

theorem cutoff_tsupport (i:Fin 4) :
    tsupport (cutoff i)⊆Set.Icc (1/4:ℝ) 1 :=
  closure_minimal (fun _ hx=>Set.Ioo_subset_Icc_self (cutoff_support i hx)) isClosed_Icc

theorem cutoff_eventual_width (η:ℝ)(hη:0<η) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀i:Fin 4,
      tsupport (cutoff i)⊆Set.Icc (Z^(-η)) (Z^η) := by
  have ht:∀ᶠZ:ℝ in atTop,(4:ℝ)≤Z^η :=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro i x hx
  have hs:=cutoff_tsupport i hx
  have hlo:Z^(-η)≤(1/4:ℝ) := by
    rw [Real.rpow_neg (by positivity)]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<4) ht
  exact ⟨hlo.trans hs.1,hs.2.trans (by linarith)⟩

theorem window_exponent_nonneg (Z b:ℝ)(hZ:1<Z)(hb:0<b)
    (k:ℤ)(hk:k∈indices 1 b) : 0≤exponent Z k := by
  have hs:1≤dyadicScale k := ((mem_indices_iff_scale 1 b (by norm_num) hb k).mp hk).1
  exact Real.logb_nonneg hZ hs

theorem window_exponent_eventual_upper (C η:ℝ)(_hC:0<C)(hη:0<η) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(b R:ℝ),0<b→b≤C*Z^R→
      ∀k:ℤ,k∈indices 1 b→exponent Z k∈Set.Icc 0 (R+η) := by
  have ht:∀ᶠZ:ℝ in atTop,4*C≤Z^η :=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (4*C))
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro b R hb hbR k hk
  refine ⟨window_exponent_nonneg Z b hZ hb k hk,?_⟩
  have hs:=((mem_indices_iff_scale 1 b (by norm_num) hb k).mp hk).2
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [exponent_scale Z hZ,Real.rpow_add (by positivity)]
  calc
    dyadicScale k≤4*b:=hs
    _≤4*(C*Z^R):=mul_le_mul_of_nonneg_left hbR (by norm_num)
    _=(4*C)*Z^R:=by ring
    _≤Z^η*Z^R:=mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (by positivity) _)
    _=Z^R*Z^η:=mul_comm _ _

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end Source2802

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialDyadicAssemblyRetained.lean; sha256: fe0e59831f7ffdac7e8efdd688a5183b90d0c2d849e6d614c80ed915fcbc9428 -/
section Source2803
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicAssembly
open InverseInitialProfile CenteredMomentSectorLocalization CenteredMomentDyadicCount
open Filter

def retainedWindows (a b:Fin 4→ℝ)(Z D m L:ℝ) : Finset (Windows a b) :=
  Finset.univ.filter (fun k=>radialCenter m (exponent Z (k 3).val)
    (exponent Z (k 1).val) D (exponent Z (k 0).val)≤L)

def tailWindows (a b:Fin 4→ℝ)(Z D m L:ℝ) : Finset (Windows a b) :=
  Finset.univ.filter (fun k=>L<radialCenter m (exponent Z (k 3).val)
    (exponent Z (k 1).val) D (exponent Z (k 0).val))

theorem window_sum_split (a b:Fin 4→ℝ)(Z D m L:ℝ)(f:Windows a b→ℂ) :
    (∑k,f k)=(∑k∈retainedWindows a b Z D m L,f k)+
      ∑k∈tailWindows a b Z D m L,f k := by
  simpa only [retainedWindows,tailWindows,not_le] using
    (Finset.sum_filter_add_sum_filter_not (Finset.univ:Finset (Windows a b))
      (fun k=>radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D
        (exponent Z (k 0).val)≤L) f).symm

theorem retained_exponents_eventually (b R Λ:ℝ)(hb:0<b)(hR:0≤R)(hΛ:0≤Λ) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀D m L T:ℝ,D≤R→0≤m→L≤Λ→0<T→
      ∀k∈retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L,
        ∀i,exponent Z (k i).val∈Set.Icc 0 (3*R+Λ+1) := by
  filter_upwards [window_exponent_eventual_upper b 1 hb (by norm_num)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro D m L T hD hm hL hT k hk
  have hs:radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D
      (exponent Z (k 0).val)≤L := (Finset.mem_filter.mp hk).2
  have hp:0<b*Z^D := mul_pos hb (Real.rpow_pos_of_pos (by linarith [hZ.1]) D)
  have h0:=hZ.2 (b*Z^D) D hp le_rfl (k 0).val (k 0).property
  have h1:=hZ.2 (b*Z^D) D hp le_rfl (k 1).val (k 1).property
  have h2:=hZ.2 (b*Z^D) D hp le_rfl (k 2).val (k 2).property
  have h3:=window_exponent_nonneg Z T hZ.1 hT (k 3).val (k 3).property
  unfold radialCenter at hs
  intro i
  fin_cases i
  · change exponent Z (k 0).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h0.1,by linarith [h0.2]⟩
  · change exponent Z (k 1).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h1.1,by linarith [h1.2]⟩
  · change exponent Z (k 2).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h2.1,by linarith [h2.2]⟩
  · change exponent Z (k 3).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h3,by linarith [h0.1,h1.2]⟩

theorem window_quotient_eventually (b R:ℝ)(hb:0<b) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀D T η:ℝ,D≤R→0<T→η≤1→
      ∀k:Windows (fun _=>1) (physicalCaps b Z D T),
        exponent Z (k 0).val-exponent Z (k 1).val+2*η≤R+3 := by
  filter_upwards [window_exponent_eventual_upper b 1 hb (by norm_num)] with Z hz
  refine ⟨hz.1,?_⟩
  intro D T η hD hT hη k
  have hp:0<b*Z^D := mul_pos hb (Real.rpow_pos_of_pos (by linarith [hz.1]) D)
  have h0:=hz.2 (b*Z^D) D hp le_rfl (k 0).val (k 0).property
  have h1:=hz.2 (b*Z^D) D hp le_rfl (k 1).val (k 1).property
  linarith [h0.2,h1.1]

theorem retained_card_of_exponents (a b:Fin 4→ℝ)(Z D m L A:ℝ)(hZ:1<Z)
    (he:∀k∈retainedWindows a b Z D m L,∀i,exponent Z (k i).val∈Set.Icc 0 A) :
    (retainedWindows a b Z D m L).card≤
      Fintype.card (Windows (fun _=>1) (fun _=>Z^A)) := by
  have hZp:0<Z := by linarith
  let f:↥(retainedWindows a b Z D m L)→Windows (fun _=>1) (fun _=>Z^A) :=
    fun k i=>⟨(k.val i).val,(mem_indices_iff_scale 1 (Z^A) (by norm_num)
      (Real.rpow_pos_of_pos hZp A) (k.val i).val).mpr ⟨by
        rw [←exponent_scale Z hZ]
        simpa only [Real.rpow_zero] using
          (Real.rpow_le_rpow_left_iff hZ).mpr (he k.val k.property i).1,by
        have hh:(dyadicScale (k.val i).val)≤Z^A := by
          rw [←exponent_scale Z hZ]
          exact (Real.rpow_le_rpow_left_iff hZ).mpr (he k.val k.property i).2
        exact hh.trans (by nlinarith [Real.rpow_pos_of_pos hZp A])⟩⟩
  have hf:Function.Injective f := by
    intro k l h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    simpa only [f] using congrArg Subtype.val (congrFun h i)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem retained_card_subpower (b R Λ ε:ℝ)(hb:0<b)(hR:0≤R)(hΛ:0≤Λ)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in atTop,
      ∀D m L T:ℝ,D≤R→0≤m→L≤Λ→0<T→
        ((retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L).card:ℝ)≤A*Z^ε := by
  obtain ⟨A,hA,hcount⟩:=windows_card_subpower 1 (3*R+Λ+1) ε (by norm_num) (by positivity) hε
  refine ⟨A,hA,?_⟩
  filter_upwards [retained_exponents_eventually b R Λ hb hR hΛ,hcount] with Z hz hc
  intro D m L T hD hm hL hT
  have he:=hz.2 D m L T hD hm hL hT
  have hi:=retained_card_of_exponents (fun _=>1) (physicalCaps b Z D T) Z D m L
    (3*R+Λ+1) hz.1 he
  have hp:(1:ℝ)≤Z^(3*R+Λ+1) := Real.one_le_rpow (le_of_lt hz.1) (by positivity)
  exact (by exact_mod_cast hi :
    ((retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L).card:ℝ)≤
      (Fintype.card (Windows (fun _=>1) (fun _=>Z^(3*R+Λ+1))):ℝ)).trans
    (hc (fun _=>1) (fun _=>Z^(3*R+Λ+1)) (by intro i; norm_num)
      (fun _=>hp) (by intro i; simp))

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end Source2803

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialRetainedSum.lean; sha256: 365f44a9e7db00199d36a76da958921350547429b92931dba9d0ee5235a589d1 -/
section Source2804
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialRetainedSum
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseSecondChildWindows Filter
local notation "O"=>ActualEisensteinCubic.O

theorem retained_sum_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
    ∀(D m r T:ℝ),0≤m→0<T→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤c₁→c₁≤bcap→1≤c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖∑k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ),
        windowBlock p hp hcop hg Finset.univ
          (cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)) w Ψ
          (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
          (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
        C*Z^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  have hb:0<max 1 b₀:=zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨J,Btree,Tclip,hBtree,hTclip,hwindow⟩:=
    InverseInitialRetainedWindow.retained_window_bound W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ Φ
      (fun _=>1/4) (fun _=>1) (by intros;norm_num) (by intros;norm_num)
      cap gap eps (cap+3) π hcap hgap heps (by linarith) hπ K
  obtain ⟨A,hA,hcount⟩:=retained_card_subpower (max 1 b₀) cap (4*η+τ) loss hb hcap (by positivity) hloss
  have hpowers:∀ᶠZ:ℝ in atTop,(4:ℝ)≤Z^η:=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop 4)
  have hlogs:∀ᶠZ:ℝ in atTop,Tclip≤3*η*Real.log Z:=by
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Tclip/(3*η)))] with Z hZ
    exact (div_le_iff₀ (by positivity : 0<3*η)).mp hZ |>.trans_eq (mul_comm _ _)
  have hevent:=window_exponent_eventual_upper (max 1 b₀) 1 hb (by norm_num)
  obtain ⟨Zaux,haux⟩:=eventually_atTop.mp (hcount.and (hpowers.and (hlogs.and hevent)))
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Zq,hC,hZq,hw⟩:=hwindow q hq
  refine ⟨A*C,max Zq Zaux,mul_pos hA hC,lt_max_of_lt_left hZq,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf D m r T hm hT
    hprodj hprod hDeq hmargin₁ hmargin₂ hparent c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hweight
  have hZq':Zq≤Z:=(le_max_left _ _).trans hZ
  obtain ⟨hcZ,hpow,hlog,hexp⟩:=haux Z ((le_max_right _ _).trans hZ)
  have hZp:1<Z:=hZq.trans_le hZq'
  have hDcap:D≤cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq]
    linarith
  let Sc:=cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)
  have hdivc:∀x∈Sc,x.divisor⊆x.common:=fun x hx=>hdiv x (Finset.mem_filter.mp hx).1
  have hfc:∀x∈Sc,x.frequency≠0:=fun x hx=>hf x (Finset.mem_filter.mp hx).1
  have hlo:Z^(-η)≤(1/4:ℝ):=by
    rw [Real.rpow_neg (zero_lt_one.trans hZp).le]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<4) hpow
  have hnorm (k:Windows (fun _=>1) (physicalCaps (max 1 b₀) Z D T))
      (hk:k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ)):
      ‖windowBlock p hp hcop hg Finset.univ Sc w Ψ (assignedElement assigned qelem)
        (primeMark (all\assigned) lists coeff) (clippedSource W₁ c₁ θ₁)
        (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
        C*Z^(m+15*η+π+eps)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=by
    have hsize:0<max 1 b₀*Z^D:=mul_pos hb (Real.rpow_pos_of_pos (zero_lt_one.trans hZp) D)
    have h0:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 0).val (k 0).property
    have h1:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 1).val (k 1).property
    apply hw Z hZq' Dpool hD all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
      qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod Sc hdivc hfc cutoff
      (fun i x hx=>Set.Ioo_subset_Icc_self (cutoff_support i hx))
      D (exponent Z (k 0).val) (exponent Z (k 2).val) (exponent Z (k 1).val)
      (exponent Z (k 3).val) m r η τ hη.le hηsmall hτsmall
      (fun _=>by linarith) hlo hlog hprodj hprod hDeq hmargin₁ hmargin₂ hparent
      (by linarith [h0.2,h1.1]) (Finset.mem_filter.mp hk).2 c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂
      (fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D (exponent Z (k 0).val)
        (exponent Z (k 2).val) (exponent Z (k 1).val) (exponent Z (k 3).val))) ?_
    intro x hx
    rw [norm_mul]
    have hmul {a b : ℝ} (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
      (mul_le_of_le_one_left hb₀ ha).trans hb
    apply hmul (hweight x (Finset.mem_filter.mp hx).1) (by positivity)
    unfold outerCutoff
    simp only [norm_mul]
    exact hmul (hmul (hmul (cutoff_norm_le _ _) (by positivity)
      (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hnorm).trans
  rw [Finset.sum_const, nsmul_eq_mul]
  calc
    _≤(A*Z^loss)*(C*Z^(m+15*η+π+eps)*
        ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))):=
      mul_le_mul_of_nonneg_right (hcZ D m (4*η+τ) T hDcap hm le_rfl hT) (by positivity)
    _=_:=by rw [Real.rpow_add (zero_lt_one.trans hZp) (m+15*η+π+eps) loss];ring

end SevenEighths.InverseInitialRetainedSum

end

end OAI

end Source2804

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialDyadicAssemblyTail.lean; sha256: 1f502c24dde6d05edfba5942739fdf10c4c1c484e1512a0f596e05c7f8ea6bf1 -/
section Source2805
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

def windowMass {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) : ℝ :=
  ∑k∈F,∏i:Fin 4,dyadicWeight (k i).val (q i)

theorem windowMass_cast {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) :
    (windowMass F q:ℂ)=∑k∈F,weight (fun i=>(k i).val) q := by
  simp only [windowMass,weight,Complex.ofReal_sum,Complex.ofReal_prod]

theorem windowMass_nonneg {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) :
    0≤windowMass F q := by
  apply Finset.sum_nonneg
  intro k hk
  exact Finset.prod_nonneg (fun i hi=>(dyadicWeight_bounds (k i).val (q i)).1)

theorem windowMass_univ (a b q:Fin 4→ℝ)(ha:∀i,0<a i)
    (hq:∀i,q i∈Set.Icc (a i) (b i)) :
    windowMass (Finset.univ:Finset (Windows a b)) q=1 := by
  apply Complex.ofReal_injective
  rw [windowMass_cast,Complex.ofReal_one]
  exact weight_partition a b q ha hq

theorem windowMass_le_one {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (ha:∀i,0<a i)(hq:∀i,q i∈Set.Icc (a i) (b i)) : windowMass F q≤1 := by
  rw [←windowMass_univ a b q ha hq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    (fun k hk hnot=>Finset.prod_nonneg (fun i hi=>(dyadicWeight_bounds (k i).val (q i)).1))

theorem windowMass_norm_le_one {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (ha:∀i,0<a i)(hq:∀i,q i∈Set.Icc (a i) (b i)) : ‖(windowMass F q:ℂ)‖≤1 := by
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (windowMass_nonneg F q)]
    using windowMass_le_one F q ha hq

theorem windowMass_ne_zero_exists {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (h:windowMass F q≠0) : ∃k∈F,weight (fun i=>(k i).val) q≠0 := by
  have hc:(windowMass F q:ℂ)≠0:=by exact_mod_cast h
  rw [windowMass_cast] at hc
  exact Finset.exists_ne_zero_of_sum_ne_zero hc

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)
  (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem windowBlock_eq_full
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)(k:Fin 4→ℤ) :
    windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m k =
      physicalBlock p hp hcop hg (pointSource pool S)
        ((fun x=>w x*weight k (sourceNorms p x))∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  simp_rw [source_weight_cutoff p Z D hZ]
  exact (physicalBlock_windowSource p hp hcop hg pool S cutoff Z D _ _ _ _ m
    w Ψ j marks W₁ W₂ Φ).symm

theorem sum_windowBlock_eq_mass
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z) :
    (∑k∈F,windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)) =
      physicalBlock p hp hcop hg (pointSource pool S)
        ((fun x=>w x*(windowMass F (sourceNorms p x):ℂ))∘erasePoint)
        Ψ j marks W₁ W₂ Φ Z D m := by
  simp_rw [windowBlock_eq_full p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m hZ]
  unfold physicalBlock
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [Function.comp_apply]
  rw [←Finset.sum_mul,←Finset.mul_sum,←windowMass_cast]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem mass_weight_bound
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(x:Source (ι:=ι) 0)
    (hx:∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    ‖w x*(windowMass F (sourceNorms p x):ℂ)‖≤‖w x‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (windowMass_norm_le_one F _ ha hx)

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem tail_mass_live (a b:Fin 4→ℝ)(Z D m L:ℝ)(hZ:1<Z)
    (x:Source (ι:=ι) 0)
    (hn:windowMass (tailWindows a b Z D m L) (sourceNorms p x)≠0) :
    ∃k∈tailWindows a b Z D m L,
      L<radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D (exponent Z (k 0).val) ∧
      outerCutoff cutoff (sourceRelative p x Z D (exponent Z (k 0).val)
        (exponent Z (k 2).val) (exponent Z (k 1).val) (exponent Z (k 3).val))≠0 := by
  obtain ⟨k,hk,hne⟩:=windowMass_ne_zero_exists _ _ hn
  refine ⟨k,hk,(Finset.mem_filter.mp hk).2,?_⟩
  rwa [source_weight_cutoff p Z D hZ] at hne

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem tail_mass_live_bounds (a b:Fin 4→ℝ)(Z D m L:ℝ)(hZ:1<Z)
    (x:Source (ι:=ι) 0)
    (hn:windowMass (tailWindows a b Z D m L) (sourceNorms p x)≠0) :
    ∃k∈tailWindows a b Z D m L,
      L<radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D (exponent Z (k 0).val) ∧
      ∀i,sourceNorms p x i∈Set.Ioo (Z^(exponent Z (k i).val)/4) (Z^(exponent Z (k i).val)) := by
  obtain ⟨k,hk,hne⟩:=windowMass_ne_zero_exists _ _ hn
  refine ⟨k,hk,(Finset.mem_filter.mp hk).2,?_⟩
  intro i
  have hi:(dyadicWeight (k i).val (sourceNorms p x i):ℂ)≠0 :=
    Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)
  have hr:dyadicWeight (k i).val (sourceNorms p x i)≠0 := by exact_mod_cast hi
  rw [exponent_scale Z hZ]
  exact dyadicWeight_support (k i).val hr

theorem physicalBlock_filter_of_live
    (source:Finset (Point ι))(P:Point ι→Prop)(w:Point ι→ℂ)
    (Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (hP:∀x∈source,∀ρ:SecondRayIndex,
      w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m x ρ≠0→P x) :
    physicalBlock p hp hcop hg source w Ψ j marks W₁ W₂ Φ Z D m =
      physicalBlock p hp hcop hg (source.filter P) w Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hh:P x
  · rw [ite_eq_left hh]
  · rw [ite_eq_right hh]
    apply Finset.sum_eq_zero
    intro ρ hρ
    by_contra hn
    exact hh (hP x hx ρ hn)

theorem physicalBlock_mass_filter
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*(windowMass F (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg
      (pointSource pool (S.filter (fun x=>windowMass F (sourceNorms p x)≠0)))
      ((fun x=>w x*(windowMass F (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hn:windowMass F (sourceNorms p x)=0
  · simp only [hn,ne_eq,not_true_eq_false,ite_false,Function.comp_apply,
      erase_sourcePoint,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]
  · rw [ite_eq_left hn]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem exists_source_frequency_cap (S:Finset (Source (ι:=ι) 0)) :
    ∃T:ℝ,0<T ∧ ∀x∈S,sourceNorms p x 3≤T := by
  have hn (x:Source (ι:=ι) 0) : 0≤sourceNorms p x 3 := by
    change 0≤‖ConcreteTraceCRT.eisEmbedding x.frequency‖^2
    positivity
  have hs:0≤∑x∈S,sourceNorms p x 3:=Finset.sum_nonneg (fun x hx=>hn x)
  refine ⟨1+∑x∈S,sourceNorms p x 3,by linarith,?_⟩
  intro x hx
  have he:sourceNorms p x 3≤∑y∈S,sourceNorms p y 3 :=
    Finset.single_le_sum (fun y hy=>hn y) hx
  linarith

theorem actual_physical_retained_tail
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m b T L:ℝ)(hZ:1<Z)
    (hW₁:Function.support W₁⊆Set.Iic b)(hW₂:Function.support W₂⊆Set.Iic b)
    (hT:∀x∈S,sourceNorms p x 3≤T) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    (∑k∈retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L,
      windowBlock p hp hcop hg pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T))
        w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)) +
    physicalBlock p hp hcop hg
      (pointSource pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T)))
      ((fun x=>w x*(windowMass (tailWindows (fun _=>1) (physicalCaps b Z D T) Z D m L)
        (sourceNorms p x):ℂ))∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  rw [actual_physical_partition p hp hcop hg hpr pool S hdiv hf w Ψ j marks W₁ W₂ Φ
    Z D m b T hZ hW₁ hW₂ hT]
  rw [window_sum_split (fun _=>1) (physicalCaps b Z D T) Z D m L]
  congr 1
  exact sum_windowBlock_eq_mass p hp hcop hg pool
    (cappedSource p S (fun _=>1) (physicalCaps b Z D T)) _ _ _ w Ψ j marks W₁ W₂ Φ Z D m hZ

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end Source2805

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailKernel.lean; sha256: a0a67a2759104a32711f23a8c767b1dc44daffadfe34d523ef8a77198ea15c3e -/
section Source2806
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open InverseInitialProfile
local notation "O" => ActualEisensteinCubic.O

private theorem finite_sum_le_tsum_subtype (F : Finset O) (P : O → Prop)
    (hF : ∀ h ∈ F, P h) (b : O → ℝ) (hb : ∀ h, 0 ≤ b h)
    (hs : Summable (fun h : {h // P h} => b h.val)) :
    (∑ h ∈ F, b h) ≤ ∑' h : {h // P h}, b h.val := by
  let f : F → {h // P h} := fun h => ⟨h.val, hF h.val h.property⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {h // P h} => z.val) h)
  rw [← Finset.sum_coe_sort F]
  have ht : Summable (fun h : F => b h.val) := (hasSum_fintype _).summable
  simpa only [tsum_fintype] using
    ht.tsum_le_tsum_of_inj f hf (fun h _ => hb h.val) (fun _ => le_rfl) hs

theorem finite_radial_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (Φ : 𝓢(ℝ,ℂ)) (K T Γ : ℝ), 0<K → 0≤T → 0≤Γ →
    ∀ (F : Finset O) (a : O→ℂ),
    (∀h∈F,T≤K*‖eisEmbedding h‖^2) →
    (∀h∈F,‖a h‖≤Γ) →
    ‖∑h∈F,a h*paperRadialFourier Φ (K*‖eisEmbedding h‖^2)‖ ≤
      Γ*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 K)^2*(1+T)^A) := by
  obtain ⟨s,C,hC,hbound⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro Φ K T Γ hK hT hΓ F a hF ha
  have hsum := finite_sum_le_tsum_subtype F
    (fun h => T ≤ K * ‖eisEmbedding h‖^2) hF
    (fun h => ‖paperRadialFourier Φ (K * ‖eisEmbedding h‖^2)‖)
    (fun _ => norm_nonneg _)
    ((paperRadialFourier_lattice_summable_norm Φ K hK).subtype
      (fun h => T ≤ K * ‖eisEmbedding h‖^2))
  calc
    _ ≤ ∑h∈F,‖a h*paperRadialFourier Φ (K*‖eisEmbedding h‖^2)‖ := norm_sum_le _ _
    _ ≤ ∑h∈F,Γ*‖paperRadialFourier Φ (K*‖eisEmbedding h‖^2)‖ := by
      apply Finset.sum_le_sum
      intro h hh
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (ha h hh) (norm_nonneg _)
    _ = Γ*∑h∈F,‖paperRadialFourier Φ (K*‖eisEmbedding h‖^2)‖ := by rw [Finset.mul_sum]
    _ ≤ Γ*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ /
        ((min 1 K)^2*(1+T)^A)) :=
      mul_le_mul_of_nonneg_left (hsum.trans (hbound Φ K T hK hT)) hΓ
    _ = _ := by ring

theorem physicalKernel_frequency (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z D m C d v n₁ n₂ : ℝ) (h : O) :
    physicalKernel W₁ W₂ Φ Z D m ![C,d,v,‖eisEmbedding h‖^2,n₁,n₂] =
      ((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)*
      W₁ (C*v*n₁/Z^D)*W₂ (C*v*n₂/Z^D)*
      paperRadialFourier Φ ((Z^m/(d*v^2*n₁*n₂))*‖eisEmbedding h‖^2) := by
  simp [physicalKernel, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem physical_frequency_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
      (Z D m C d v n₁ n₂ T Γ : ℝ),
    0<Z → 0<d → 0<v → 0<n₁ → 0<n₂ → 0≤T → 0≤Γ →
    ∀ (F : Finset O) (a : O→ℂ),
    (∀h∈F,T≤(Z^m/(d*v^2*n₁*n₂))*‖eisEmbedding h‖^2) →
    (∀h∈F,‖a h‖≤Γ) →
    ‖∑h∈F,a h*physicalKernel W₁ W₂ Φ Z D m
      ![C,d,v,‖eisEmbedding h‖^2,n₁,n₂]‖ ≤
      Γ*‖((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)*
        W₁ (C*v*n₁/Z^D)*W₂ (C*v*n₂/Z^D)‖ *
      (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/(d*v^2*n₁*n₂)))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hbound⟩ := finite_radial_tail A
  refine ⟨s,C₀,hC₀,?_⟩
  intro W₁ W₂ Φ Z D m C d v n₁ n₂ T Γ hZ hd hv hn₁ hn₂ hT hΓ F a hF ha
  let b : ℂ := ((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)*
        W₁ (C*v*n₁/Z^D)*W₂ (C*v*n₂/Z^D)
  simp_rw [physicalKernel_frequency,←mul_assoc]
  simpa only [b,←mul_assoc] using hbound Φ (Z^m/(d*v^2*n₁*n₂)) T (Γ*‖b‖) (by positivity) hT
    (by positivity) F (fun h=>a h*b) hF (by
      intro h hh
      exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right (ha h hh) (norm_nonneg _)))

theorem correlated_scale_lower (Y C d v n₁ n₂ L : ℝ)
    (hY : 0<Y) (hC : 0<C) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂) (hL : 0<L)
    (h₁ : C*v*n₁≤L) (h₂ : C*v*n₂≤L) :
    Y*C^2/(d*L^2) ≤ Y/(d*v^2*n₁*n₂) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh := mul_le_mul h₁ h₂ (by positivity) hL.le
  nlinarith [mul_le_mul_of_nonneg_left hh (show 0≤Y*d by positivity)]

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end Source2806

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailGeometry.lean; sha256: f6082d286dfaf1d362669b3ee17d19f73cde7299e1c71832d47be981b1d28dfe -/
section Source2807
namespace OAI

noncomputable section

open scoped Classical SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open InverseInitialProfile

theorem live_column_norm_bound (W : ℝ→ℂ) (b C v n X : ℝ)
    (hs : Function.support W⊆Set.Iic b) (hX : 0<X)
    (hw : W (C*v*n/X)≠0) : C*v*n≤b*X := by
  exact (div_le_iff₀ hX).mp (hs hw)

theorem actual_radial_center_lower
    (Z D m B θ H η C d v n₁ n₂ L hnorm : ℝ)
    (hZ : 1≤Z) (hd : 0<d) (hv : 0<v) (hn₁ : 0<n₁) (hn₂ : 0<n₂)
    (hL : 0<L) (hC : Z^B≤C) (hdiv : d≤Z^(θ+η))
    (hcol : L≤Z^(D+η)) (hfreq : Z^H≤hnorm)
    (h₁ : C*v*n₁≤L) (h₂ : C*v*n₂≤L) :
    Z^(radialCenter m H θ D B-3*η) ≤
      (Z^m/(d*v^2*n₁*n₂))*hnorm := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hc : 0<C := (Real.rpow_pos_of_pos hz B).trans_le hC
  have hh : 0≤hnorm := (Real.rpow_pos_of_pos hz H).le.trans hfreq
  have hscale := correlated_scale_lower (Z^m) C d v n₁ n₂ L
    (by positivity) hc hd hv hn₁ hn₂ hL h₁ h₂
  calc
    _ = Z^m*(Z^B)^2*Z^H/(Z^(θ+η)*(Z^(D+η))^2) := by
      simp only [pow_two]
      rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,
        ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_sub hz]
      congr 1
      unfold radialCenter
      ring
    _ ≤ Z^m*C^2*hnorm/(d*L^2) := by
      gcongr
    _ = (Z^m*C^2/(d*L^2))*hnorm := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale hh

theorem high_radial_block_tail_gate
    (Z D m B θ H η τ C d v n₁ n₂ L hnorm : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂) (hL : 0<L)
    (hC : Z^B≤C) (hdiv : d≤Z^(θ+η))
    (hcol : L≤Z^(D+η)) (hfreq : Z^H≤hnorm)
    (h₁ : C*v*n₁≤L) (h₂ : C*v*n₂≤L)
    (hhigh : 4*η+τ≤radialCenter m H θ D B) :
    Z^τ ≤ (Z^m/(d*v^2*n₁*n₂))*hnorm := by
  exact (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)).trans
    (actual_radial_center_lower Z D m B θ H η C d v n₁ n₂ L hnorm
      hZ hd hv hn₁ hn₂ hL hC hdiv hcol hfreq h₁ h₂)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end Source2807

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailAnnulus.lean; sha256: 3e2067301ea25299dd7be9df4da0fae339d7844a7bbac3e988bfcd20f231d6c3 -/
section Source2808
namespace OAI

noncomputable section

namespace SevenEighths.InverseInitialHighFrequencyTail
open InverseInitialProfile

theorem actual_annulus_radial_lower
    (Z D m B θ H b C d v n₁ n₂ hnorm : ℝ)
    (hZ : 0<Z) (hb : 0<b) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂)
    (hC : Z^B/4≤C) (hdiv : d≤Z^θ) (hfreq : Z^H/4≤hnorm)
    (h₁ : C*v*n₁≤b*Z^D) (h₂ : C*v*n₂≤b*Z^D) :
    Z^(radialCenter m H θ D B)/(64*b^2) ≤
      (Z^m/(d*v^2*n₁*n₂))*hnorm := by
  have hc : 0<C := (show 0<Z^B/4 by positivity).trans_le hC
  have hh : 0≤hnorm := (show 0≤Z^H/4 by positivity).trans hfreq
  have hscale := correlated_scale_lower (Z^m) C d v n₁ n₂ (b*Z^D)
    (by positivity) hc hd hv hn₁ hn₂ (by positivity) h₁ h₂
  have he : Z^m*(Z^B)^2*Z^H/(Z^θ*(Z^D)^2)=Z^(radialCenter m H θ D B) := by
    simp only [pow_two]
    rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,
      ←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
    congr 1
    unfold radialCenter
    ring
  calc
    _ = Z^m*(Z^B/4)^2*(Z^H/4)/(Z^θ*(b*Z^D)^2) := by
      rw [←he]
      ring
    _ ≤ Z^m*C^2*hnorm/(d*(b*Z^D)^2) := by gcongr
    _ = (Z^m*C^2/(d*(b*Z^D)^2))*hnorm := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale hh

theorem actual_annulus_high_gate
    (Z D m B θ H η τ b C d v n₁ n₂ hnorm : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hb : 0<b) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂)
    (hC : Z^B/4≤C) (hdiv : d≤Z^θ) (hfreq : Z^H/4≤hnorm)
    (h₁ : C*v*n₁≤b*Z^D) (h₂ : C*v*n₂≤b*Z^D)
    (hfixed : 64*b^2≤Z^η) (hhigh : 4*η+τ≤radialCenter m H θ D B) :
    Z^τ≤(Z^m/(d*v^2*n₁*n₂))*hnorm := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  apply le_trans _ (actual_annulus_radial_lower Z D m B θ H b C d v n₁ n₂ hnorm
    hz hb hd hv hn₁ hn₂ hC hdiv hfreq h₁ h₂)
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    Z^τ*(64*b^2)≤Z^τ*Z^η := mul_le_mul_of_nonneg_left hfixed (by positivity)
    _ = Z^(τ+η) := (Real.rpow_add hz τ η).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end Source2808

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailWeights.lean; sha256: 985b3dd2f79bee9505e4e2d0d195d7c9c738901e11ca606efecb4badc18d442d -/
section Source2809
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialEnergyCallerWeights
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι]

theorem marked_support_norm_bound
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hdis : (slots:Set σ).PairwiseDisjoint lists)
    (ha : ∀i∈slots,∀k∈lists i,‖a i k‖≤1)
    (S : Finset ι) (L : ℝ) (hL : 1≤L) (hS : primeProductNorm p S≤L) :
    ‖primeMark slots lists a S‖≤128*L := by
  have heq : boundedPrimeSupports p S L=S.powerset := by
    apply Finset.filter_eq_self.mpr
    intro U hU
    exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hU)).trans hS
  have hc := boundedPrimeSupports_card p hinj S L hL
  rw [heq,Finset.card_powerset] at hc
  exact (primeMark_norm_le_divisor_count slots lists a S hdis ha).trans (by exact_mod_cast hc)

theorem initialColumn_mark_factor
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (Ψ : O→*ℂ) (j C d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    initialColumn p hp hcop hg Ψ j C d h H S =
      initialColumn p hp hcop hg Ψ j C d h (fun _=>1) S * H S := by
  simp only [initialColumn,mul_one]

theorem initialColumn_mark_norm
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (hΨ : ∀n,‖Ψ n‖≤1)
    (j C d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    ‖initialColumn p hp hcop hg Ψ j C d h H S‖≤‖H S‖ := by
  rw [initialColumn_mark_factor,norm_mul]
  exact (mul_le_mul_of_nonneg_right
    ((initialColumn_norm_le p hp hcop hg hc Ψ j C d h S).trans (hΨ _))
    (norm_nonneg _)).trans_eq (one_mul _)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end Source2809

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailSource.lean; sha256: 15a66dbf5c8336320153c7f2ea4cd2a7f9ef7a0a21e4e224463683bbb2ffa75c -/
section Source2810
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialPhysicalMeasure
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def sourceKey (x : Point ι) : Fin 5→Finset ι :=
  ![x.common,x.divisor,x.overlap,x.left,x.right]

def sourcePoint (k : Fin 5→Finset ι) (h : O) : Point ι :=
  ⟨k 0,k 1,k 2,k 3,k 4,h⟩

omit [DecidableEq ι] in
theorem sourcePoint_key (x : Point ι) : sourcePoint (sourceKey x) x.frequency=x := by
  cases x
  rfl

def sourceKeys (S : Finset (Point ι)) : Finset (Fin 5→Finset ι) := S.image sourceKey

def sourceFrequencies (S : Finset (Point ι)) (k : Fin 5→Finset ι) : Finset O :=
  (S.filter (fun x=>sourceKey x=k)).image Point.frequency

theorem mem_sourceFrequencies (S : Finset (Point ι)) (k : Fin 5→Finset ι) (h : O) :
    h∈sourceFrequencies S k ↔ sourcePoint k h∈S := by
  constructor
  · intro hh
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hh
    obtain ⟨hx,hk⟩ := Finset.mem_filter.mp hx
    rw [←hk,←he,sourcePoint_key]
    exact hx
  · intro hh
    apply Finset.mem_image.mpr
    refine ⟨sourcePoint k h,Finset.mem_filter.mpr ⟨hh,?_⟩,rfl⟩
    funext i
    fin_cases i <;> rfl

theorem source_sum_fibers (S : Finset (Point ι)) (f : Point ι→ℂ) :
    ∑x∈S,f x = ∑k∈sourceKeys S,∑h∈sourceFrequencies S k,f (sourcePoint k h) := by
  rw [←Finset.sum_fiberwise_of_maps_to (s:=S) (t:=sourceKeys S) (g:=sourceKey)
    (fun x hx=>Finset.mem_image.mpr ⟨x,hx,rfl⟩) f]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sourceFrequencies,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [←(Finset.mem_filter.mp hx).2,sourcePoint_key]
  · intro x hx y hy hxy
    have hk := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    rw [←sourcePoint_key x,←sourcePoint_key y,hk,hxy]

theorem sourceKeys_card
    (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (S : Finset (Point ι)) (L : ℝ) (hL : 1≤L)
    (hpool : ∀x∈S,∀i,sourceKey x i⊆pool)
    (hnorm : ∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤L) :
    ((sourceKeys S).card:ℝ)≤(128*L)^5 := by
  let T := boundedPrimeSupports p pool L
  have hsub : sourceKeys S⊆Fintype.piFinset (fun _ : Fin 5=>T) := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hpool x hx i),hnorm x hx i⟩
  have hc := Finset.card_le_card hsub
  have hcast : ((sourceKeys S).card:ℝ)≤(T.card:ℝ)^5 := by
    exact_mod_cast (by simpa using hc)
  exact hcast.trans (pow_le_pow_left₀ (by positivity)
    (boundedPrimeSupports_card p hinj pool L hL) 5)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end Source2810

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailCoefficient.lean; sha256: 8e0394d6b9ecb3e6b1c852c531c8893468552381b950b70089cbb28e0e9f5d63 -/
section Source2811
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerWeights InverseInitialProfile InverseInitialKernelBridge InverseInitialRayAttachment
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def originalCoefficient (Ψ : O→*ℂ) (j : O) (mark : Finset ι→ℂ)
    (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  (initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius (fun i=>Ideal.span {p i}) x.overlap * secondRayCoefficient ρ) *
  star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) x.frequency (fun A=>mark (x.common∪A)) (x.overlap∪x.left)) *
  initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=>mark (x.common∪A)) (x.overlap∪x.right)

include hp hcop hg in
theorem physicalTerm_original_coefficient
    (Ψ : O→*ℂ) (j : O) (mark : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : SchwartzMap ℝ ℂ) (Z D m : ℝ)
    (x : Point ι) (hx : Valid x) (ρ : SecondRayIndex) :
    physicalTerm p hp hcop hg Ψ j mark W₁ W₂ Φ Z D m x ρ =
      originalCoefficient p hp hcop hg Ψ j mark x ρ *
      physicalKernel W₁ W₂ Φ Z D m (coordinates p x) := by
  unfold physicalTerm
  rw [sourceIdeal_union p _ _ hx.overlap_left,sourceIdeal_union p _ _ hx.overlap_right,
    physicalKernel_common_factor]
  rfl

include hp hcop hg in
theorem originalCoefficient_marked_bound
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (hΨ : ∀n,‖Ψ n‖≤1) (j : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hdis : (slots:Set σ).PairwiseDisjoint lists)
    (ha : ∀i∈slots,∀k∈lists i,‖a i k‖≤1)
    (x : Point ι) (ρ : SecondRayIndex) (L : ℝ) (hL : 1≤L)
    (hleft : primeProductNorm p x.common*primeProductNorm p x.overlap*
      primeProductNorm p x.left≤L)
    (hright : primeProductNorm p x.common*primeProductNorm p x.overlap*
      primeProductNorm p x.right≤L) :
    ‖originalCoefficient p hp hcop hg Ψ j (primeMark slots lists a) x ρ‖≤
      ‖secondRayCoefficient ρ‖*(128*L)^2 := by
  have hmark (N : Finset ι)
      (hN : primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p N≤L) :
      ‖primeMark slots lists a (x.common∪(x.overlap∪N))‖≤128*L := by
    apply marked_support_norm_bound p hp hinj slots lists a hdis ha _ L hL
    apply (primeProductNorm_union_le_mul p hp _ _).trans
    apply (mul_le_mul_of_nonneg_left (primeProductNorm_union_le_mul p hp _ _)
      (primeProductNorm_pos p hp _).le).trans
    simpa only [mul_assoc] using hN
  have hl := (initialColumn_mark_norm p hp hcop hg hc (secondRayMinus Ψ ρ)
    (fun n=>(secondRayMinus_norm_le Ψ ρ n).trans (hΨ n)) j (∏i∈x.common,p i)
    (divisor p x) x.frequency (fun A=>primeMark slots lists a (x.common∪A))
    (x.overlap∪x.left)).trans (hmark x.left hleft)
  have hr := (initialColumn_mark_norm p hp hcop hg hc (secondRayPlus Ψ ρ)
    (fun n=>(secondRayPlus_norm_le Ψ ρ n).trans (hΨ n)) j (∏i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=>primeMark slots lists a (x.common∪A))
    (x.overlap∪x.right)).trans (hmark x.right hright)
  have hb := initialBeta_norm_le_one p Ψ hΨ j x.common
  have hm := QuadraticInitialBound.norm_ideal_moebius_le_one (sourceIdeal p x.divisor)
  have hv : ‖supportMobius (fun i=>Ideal.span {p i}) x.overlap‖≤1 :=
    QuadraticInitialBound.norm_ideal_moebius_le_one _
  simp only [originalCoefficient,norm_mul,norm_star]
  calc
    _ ≤ 1*1*1*‖secondRayCoefficient ρ‖*(128*L)*(128*L) := by gcongr
    _ = _ := by ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end Source2811

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailScale.lean; sha256: 22064f0d4ba0646ca1d017d4544f1d18bf5ed8fe118ac5f5bfa897c5955190f8 -/
section Source2812
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT InverseInitialProfile
local notation "O"=>ActualEisensteinCubic.O

theorem initial_denominator_bound (C d v n₁ n₂ L : ℝ)
    (hC : 1≤C) (_hd : 0≤d) (hv : 0≤v) (hn₁ : 0≤n₁) (hn₂ : 0≤n₂)
    (hL : 0≤L) (hdL : d≤L) (h₁ : C*v*n₁≤L) (h₂ : C*v*n₂≤L) :
    d*v^2*n₁*n₂≤L^3 := by
  have h₁' : v*n₁≤L := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hv hn₁)]
  have h₂' : v*n₂≤L := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hv hn₂)]
  have hh := mul_le_mul h₁' h₂' (mul_nonneg hv hn₂) hL
  have he := mul_le_mul hdL hh (by positivity) hL
  nlinarith

theorem initial_scalar_bound (Z D m d v n₁ n₂ : ℝ) (hZ : 0<Z)
    (hd : 1≤d) (hv : 1≤v) (hn₁ : 1≤n₁) (hn₂ : 1≤n₂) :
    ‖((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)‖≤Z^(m-D) := by
  have hroot : 1≤Real.sqrt (n₁*n₂) := by
    rw [Real.one_le_sqrt]
    exact one_le_mul_of_one_le_of_one_le hn₁ hn₂
  have hden : 1≤d*v*Real.sqrt (n₁*n₂) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hd hv) hroot
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have h := div_le_self (show 0≤Z^(-D)*Z^m by positivity) hden
  apply h.trans_eq
  rw [←Real.rpow_add hZ]
  congr 1
  ring

theorem physical_frequency_tail_uniform (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
      (Z D m C d v n₁ n₂ L T Γ B₁ B₂ : ℝ),
    0<Z → 1≤C → 1≤d → 1≤v → 1≤n₁ → 1≤n₂ → 1≤L →
    d≤L → C*v*n₁≤L → C*v*n₂≤L → 0≤T → 0≤Γ → 0≤B₁ → 0≤B₂ →
    ‖W₁ (C*v*n₁/Z^D)‖≤B₁ → ‖W₂ (C*v*n₂/Z^D)‖≤B₂ →
    ∀ (F : Finset O) (a : O→ℂ),
    (∀h∈F,T≤(Z^m/(d*v^2*n₁*n₂))*‖eisEmbedding h‖^2) →
    (∀h∈F,‖a h‖≤Γ) →
    ‖∑h∈F,a h*physicalKernel W₁ W₂ Φ Z D m
      ![C,d,v,‖eisEmbedding h‖^2,n₁,n₂]‖ ≤
      Γ*Z^(m-D)*B₁*B₂*(C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hbound⟩ := physical_frequency_tail A
  refine ⟨s,C₀,hC₀,?_⟩
  intro W₁ W₂ Φ Z D m C d v n₁ n₂ L T Γ B₁ B₂ hZ hC hd hv hn₁ hn₂ hL
    hdL h₁ h₂ hT hΓ hB₁ hB₂ hw₁ hw₂ F a hF ha
  have hd0 : 0<d := zero_lt_one.trans_le hd
  have hv0 : 0<v := zero_lt_one.trans_le hv
  have hn₁0 : 0<n₁ := zero_lt_one.trans_le hn₁
  have hn₂0 : 0<n₂ := zero_lt_one.trans_le hn₂
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hden := initial_denominator_bound C d v n₁ n₂ L hC hd0.le hv0.le hn₁0.le hn₂0.le hL0.le hdL h₁ h₂
  have hK : Z^m/L^3≤Z^m/(d*v^2*n₁*n₂) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hscalar := initial_scalar_bound Z D m d v n₁ n₂ hZ hd hv hn₁ hn₂
  apply (hbound W₁ W₂ Φ Z D m C d v n₁ n₂ T Γ hZ hd0 hv0 hn₁0 hn₂0 hT hΓ F a hF ha).trans
  simp only [norm_mul]
  have hnorm : ‖((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)‖*
      ‖W₁ (C*v*n₁/Z^D)‖*‖W₂ (C*v*n₂/Z^D)‖ ≤ Z^(m-D)*B₁*B₂ := by gcongr
  calc
    _ ≤ Γ*(Z^(m-D)*B₁*B₂)*(C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
      gcongr
    _ = _ := by ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end Source2812

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailFiber.lean; sha256: cc5150cbb5fdea29e04f703db3435ddfa65ada9f5b93ae9130dfddeeb99c9a32 -/
section Source2813
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialKernelBridge InverseInitialProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def keyNorms (p : ι→O) (k : Fin 5→Finset ι) : Fin 5→ℝ :=
  fun i=>primeProductNorm p (k i)

omit [DecidableEq ι] in
theorem coordinates_sourcePoint (p : ι→O) (k : Fin 5→Finset ι) (h : O) :
    coordinates p (sourcePoint k h)=
      ![keyNorms p k 0,keyNorms p k 1,keyNorms p k 2,‖eisEmbedding h‖^2,
        keyNorms p k 3,keyNorms p k 4] := by
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
    rfl
  funext i
  fin_cases i <;> simp [coordinates,sourcePoint,physicalCoordinates,keyNorms,hn]

theorem original_frequency_fiber_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L T Γ B₁ B₂ : ℝ),
    0<Z → 1≤L → 0≤T → 0≤Γ → 0≤B₁ → 0≤B₂ →
    (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    ∀ (k : Fin 5→Finset ι) (F : Finset O) (w : Point ι→ℂ) (ρ : SecondRayIndex),
    keyNorms p k 1≤L →
    keyNorms p k 0*keyNorms p k 2*keyNorms p k 3≤L →
    keyNorms p k 0*keyNorms p k 2*keyNorms p k 4≤L →
    (∀h∈F,Valid (sourcePoint k h)) → (∀h∈F,‖w (sourcePoint k h)‖≤Γ) →
    (∀h∈F,T≤(Z^m/(keyNorms p k 1*(keyNorms p k 2)^2*
      keyNorms p k 3*keyNorms p k 4))*‖eisEmbedding h‖^2) →
    ‖∑h∈F,w (sourcePoint k h)*physicalTerm p hp hcop hg Ψ j
      (primeMark slots lists a) W₁ W₂ Φ Z D m (sourcePoint k h) ρ‖ ≤
    (Γ*‖secondRayCoefficient ρ‖*(128*L)^2)*Z^(m-D)*B₁*B₂*
      (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
      ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hbound⟩ := physical_frequency_tail_uniform A
  refine ⟨s,C₀,hC₀,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc Ψ hΨ j slots lists a hdis ha
    W₁ W₂ Φ Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ k F w ρ hd hleft hright hvalid hw htail
  have hn (i : Fin 5) : 1≤keyNorms p k i := primeProductNorm_ge_one p hp _
  have he : (∑h∈F,w (sourcePoint k h)*physicalTerm p hp hcop hg Ψ j
      (primeMark slots lists a) W₁ W₂ Φ Z D m (sourcePoint k h) ρ) =
      ∑h∈F,(w (sourcePoint k h)*originalCoefficient p hp hcop hg Ψ j
        (primeMark slots lists a) (sourcePoint k h) ρ)*
        physicalKernel W₁ W₂ Φ Z D m
        ![keyNorms p k 0,keyNorms p k 1,keyNorms p k 2,‖eisEmbedding h‖^2,
          keyNorms p k 3,keyNorms p k 4] := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [physicalTerm_original_coefficient p hp hcop hg Ψ j _ W₁ W₂ Φ Z D m _ (hvalid h hh) ρ,
      coordinates_sourcePoint]
    ring
  rw [he]
  apply hbound W₁ W₂ Φ Z D m (keyNorms p k 0) (keyNorms p k 1)
    (keyNorms p k 2) (keyNorms p k 3) (keyNorms p k 4) L T
    (Γ*‖secondRayCoefficient ρ‖*(128*L)^2) B₁ B₂ hZ (hn 0) (hn 1) (hn 2)
    (hn 3) (hn 4) hL hd hleft hright hT (by positivity) hB₁ hB₂ (hW₁ _) (hW₂ _) F _ htail
  intro h hh
  rw [norm_mul]
  have hc := originalCoefficient_marked_bound p hp hcop hg hinj hc Ψ hΨ j slots lists a
    hdis ha (sourcePoint k h) ρ L hL hleft hright
  calc
    _ ≤ Γ*(‖secondRayCoefficient ρ‖*(128*L)^2) := by gcongr; exact hw h hh
    _ = _ := by ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end Source2813

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailAggregate.lean; sha256: 0510a23fbdfe4e5547082f6985d5542f014c2436f1e7fa3048ea7128a23ba591 -/
section Source2814
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open InverseInitialPhysicalMeasure

theorem original_source_norm_fibers
    {ι ρ : Type*} [DecidableEq ι]
    (S : Finset (Point ι)) (R : Finset ρ) (f : Point ι→ρ→ℂ) (b : ρ→ℝ)
    (hb : ∀k∈sourceKeys S,∀r∈R,
      ‖∑h∈sourceFrequencies S k,f (sourcePoint k h) r‖≤b r) :
    ‖∑x∈S,∑r∈R,f x r‖≤((sourceKeys S).card:ℝ)*(∑r∈R,b r) := by
  rw [source_sum_fibers]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑k∈sourceKeys S,∑r∈R,b r := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.sum_comm]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr=>hb k hk r hr))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end Source2814

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTail.lean; sha256: 76eed78283c50e90262131094eee6bcf6bcf670b7c8519fc47fe1a1ade7cfe73 -/
section Source2815
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
local notation "O"=>ActualEisensteinCubic.O

theorem original_physical_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L T Γ B₁ B₂ : ℝ),
    0<Z → 1≤L → 0≤T → 0≤Γ → 0≤B₁ → 0≤B₂ →
    (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    ∀ (pool : Finset ι) (S : Finset (Point ι)) (w : Point ι→ℂ),
    (∀x∈S,Valid x) → (∀x∈S,‖w x‖≤Γ) →
    (∀x∈S,∀i,sourceKey x i⊆pool) →
    (∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤L) →
    (∀x∈S,T≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2) →
    ‖physicalBlock p hp hcop hg S w Ψ j (primeMark slots lists a) W₁ W₂ Φ Z D m‖ ≤
      (128*L)^7*Γ*(∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖)*Z^(m-D)*B₁*B₂*
        (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hfiber⟩ := original_frequency_fiber_tail A
  refine ⟨s,C₀,hC₀,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
    Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ pool S w hvalid hw hpool hnorm hleft hright htail
  let R : ℝ := Z^(m-D)*B₁*B₂*(C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
    ((min 1 (Z^m/L^3))^2*(1+T)^A)
  have hR : 0≤R := by dsimp [R]; positivity
  let B : ℝ := Γ*(128*L)^2*R
  have hB : 0≤B := by dsimp [B]; positivity
  have hkey (k) (hk : k∈sourceKeys S) (ρ : SecondRayIndex) :
      ‖∑h∈sourceFrequencies S k,
        w (sourcePoint k h)*physicalTerm p hp hcop hg Ψ j (primeMark slots lists a)
          W₁ W₂ Φ Z D m (sourcePoint k h) ρ‖ ≤ B*‖secondRayCoefficient ρ‖ := by
    obtain ⟨x,hx,hk'⟩ := Finset.mem_image.mp hk
    have hkN (i) : keyNorms p k i=primeProductNorm p (sourceKey x i) := by rw [←hk'];rfl
    have hf (h) (hh : h∈sourceFrequencies S k) := (mem_sourceFrequencies S k h).mp hh
    have hkl : keyNorms p k 0*keyNorms p k 2*keyNorms p k 3≤L := by
      simpa [←hk',keyNorms,sourceKey] using hleft x hx
    have hkr : keyNorms p k 0*keyNorms p k 2*keyNorms p k 4≤L := by
      simpa [←hk',keyNorms,sourceKey] using hright x hx
    have htailk : ∀h∈sourceFrequencies S k,T≤(Z^m/(keyNorms p k 1*(keyNorms p k 2)^2*
        keyNorms p k 3*keyNorms p k 4))*‖eisEmbedding h‖^2 := by
      intro h hh
      simpa only [sourcePoint,keyNorms] using htail (sourcePoint k h) (hf h hh)
    have hb := hfiber p hp hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
      Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ k (sourceFrequencies S k) w ρ
      (by rw [hkN];exact hnorm x hx 1) hkl hkr
      (fun h hh=>hvalid (sourcePoint k h) (hf h hh))
      (fun h hh=>hw (sourcePoint k h) (hf h hh)) htailk
    apply hb.trans_eq
    dsimp [B,R]
    ring
  have hsum := original_source_norm_fibers S Finset.univ
    (fun x ρ=>w x*physicalTerm p hp hcop hg Ψ j (primeMark slots lists a) W₁ W₂ Φ Z D m x ρ)
    (fun ρ=>B*‖secondRayCoefficient ρ‖) (fun k hk ρ _=>hkey k hk ρ)
  change ‖∑x∈S,∑ρ : SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j
    (primeMark slots lists a) W₁ W₂ Φ Z D m x ρ‖≤_
  apply hsum.trans
  rw [←Finset.mul_sum]
  calc
    _ ≤ (128*L)^5*(B*(∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖)) :=
      mul_le_mul_of_nonneg_right (sourceKeys_card p hp hinj pool S L hL hpool hnorm) (by positivity)
    _ = _ := by dsimp [B,R]; ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end Source2815

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailPower.lean; sha256: 7884602f61a017fa1b5b0919d8edb038e9ba76ed4a8e81643aefb0e003e884e6 -/
section Source2816
namespace OAI

noncomputable section

namespace SevenEighths.InverseInitialHighFrequencyTail

theorem initial_tail_power_cost (A : ℕ) (Z L Lcap m D τ : ℝ)
    (hZ : 1≤Z) (hL : 1≤L) (hcap : 0≤Lcap) (hsize : L≤Z^Lcap)
    (hm : -m≤Lcap) (hmd : m-D≤Lcap) :
    (128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A) ≤
      128^7*Z^(16*Lcap-τ*A) := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hl : 0<L := zero_lt_one.trans_le hL
  have hbase : Z^(-4*Lcap)≤min 1 (Z^m/L^3) := by
    apply le_min
    · exact Real.rpow_le_one_of_one_le_of_nonpos hZ (by linarith)
    · calc
        _ = Z^(-Lcap)/(Z^Lcap)^3 := by
          rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
          congr 1
          norm_num
          ring
        _ ≤ Z^m/L^3 := by
          gcongr ; linarith
  calc
    _ ≤ (128*Z^Lcap)^7*Z^Lcap/((Z^(-4*Lcap))^2*(Z^τ)^A) := by
      gcongr ; linarith
    _ = 128^7*Z^(16*Lcap-τ*A) := by
      rw [mul_pow,←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,
        ←Real.rpow_mul_natCast hz.le]
      rw [mul_assoc,←Real.rpow_add hz,←Real.rpow_add hz,mul_div_assoc,
        ←Real.rpow_sub hz]
      congr 2
      norm_num
      ring

theorem initial_tail_rapid_order (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ A : ℕ, ∀ (Z L m D : ℝ), 1≤Z → 1≤L → 0≤Lcap → L≤Z^Lcap →
      -m≤Lcap → m-D≤Lcap →
      (128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A) ≤
        128^7*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((16*Lcap+saving)/τ)
  refine ⟨A,?_⟩
  intro Z L m D hZ hL hcap hsize hm hmd
  apply (initial_tail_power_cost A Z L Lcap m D τ hZ hL hcap hsize hm hmd).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have h := (div_lt_iff₀ hτ).mp hA
  nlinarith

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end Source2816

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailRapid.lean; sha256: f05c5010a354801b867c2093b4bb93a1505459e9b2339e345c65b98df1565f70 -/
section Source2817
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
local notation "O"=>ActualEisensteinCubic.O

theorem original_physical_tail_rapid (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L Γ B₁ B₂ : ℝ),
    1≤Z → 1≤L → 0≤Lcap → L≤Z^Lcap → -m≤Lcap → m-D≤Lcap → 0≤Γ → 0≤B₁ → 0≤B₂ →
    (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    ∀ (pool : Finset ι) (S : Finset (Point ι)) (w : Point ι→ℂ),
    (∀x∈S,Valid x) → (∀x∈S,‖w x‖≤Γ) →
    (∀x∈S,∀i,sourceKey x i⊆pool) →
    (∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤L) →
    (∀x∈S,Z^τ≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2) →
    ‖physicalBlock p hp hcop hg S w Ψ j (primeMark slots lists a) W₁ W₂ Φ Z D m‖ ≤
      C₀*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨A,hA⟩ := initial_tail_rapid_order Lcap saving τ hτ
  obtain ⟨s,C₀,hC₀,hraw⟩ := original_physical_tail A
  let R : ℝ := ∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖
  have hR : 0≤R := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  refine ⟨s,128^7*(R+1)*C₀,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
    Z D m L Γ B₁ B₂ hZ hL hcap hsize hm hmd hΓ hB₁ hB₂ hW₁ hW₂ pool S w
    hvalid hw hpool hnorm hleft hright htail
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hb := hraw p hp hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
    Z D m L (Z^τ) Γ B₁ B₂ hz hL (by positivity) hΓ hB₁ hB₂ hW₁ hW₂
    pool S w hvalid hw hpool hnorm hleft hright htail
  have hs : 0≤s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ := apply_nonneg _ _
  apply hb.trans
  calc
    _ = ((128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A))*
        (Γ*R*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) := by dsimp [R];ring
    _ ≤ (128^7*Z^(-saving))*(Γ*R*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) :=
      mul_le_mul_of_nonneg_right (hA Z L m D hZ hL hcap hsize hm hmd) (by positivity)
    _ ≤ (128^7*Z^(-saving))*(Γ*(R+1)*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) := by
      gcongr
      linarith
    _ = _ := by ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end Source2817

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialDyadicTailGates.lean; sha256: ffcc10359ac09964be55f02741f42fd725303a373c5ec71de6010eda2d3a6e4f -/
section Source2818
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicTailBound
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialDyadicAssembly InverseInitialProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem pointSource_erase_mem (pool : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (x : Point ι) (hx : x∈pointSource pool S) : erasePoint x∈S := by
  obtain ⟨y,hy,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  simpa only [erase_sourcePoint] using hy

theorem pointSource_supports (pool : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hC : ∀x∈S,x.common⊆pool) (hV : ∀x∈S,x.overlap⊆pool)
    (hdiv : ∀x∈S,x.divisor⊆x.common)
    (x : Point ι) (hx : x∈pointSource pool S) :
    ∀i,InverseInitialHighFrequencyTail.sourceKey x i⊆pool := by
  obtain ⟨y,hy,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  intro i
  fin_cases i
  · exact hC y hy
  · exact (hdiv y hy).trans (hC y hy)
  · exact hV y hy
  · exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).1).trans Finset.sdiff_subset
  · exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).2).trans Finset.sdiff_subset

def idealIndex : Fin 5→Fin 6 := ![0,1,2,4,5]

omit [DecidableEq ι] in
theorem sourceKey_norm_coordinate (p : ι→O) (x : Point ι) (i : Fin 5) :
    primeProductNorm p (InverseInitialHighFrequencyTail.sourceKey x i)=coordinates p x (idealIndex i) := by
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
    rfl
  fin_cases i <;> simp [InverseInitialHighFrequencyTail.sourceKey,coordinates,physicalCoordinates,idealIndex,hn]

omit [DecidableEq ι] in
theorem sourceNorms_erase (p : ι→O) (x : Point ι) (i : Fin 4) :
    sourceNorms p (erasePoint x) i=coordinates p x (InverseSecondChildWindows.outerIndex i) := by
  have he : InverseInitialEnergyCallerModes.sourcePoint (erasePoint x) x.left x.right=x := by
    cases x
    rfl
  simpa only [he] using sourceNorms_fresh p (erasePoint x) x.left x.right i

omit [DecidableEq ι] in
theorem live_mass_radial_gate
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (a b : Fin 4→ℝ) (Z D m η τ bW : ℝ) (hZ : 1<Z) (hη : 0≤η)
    (hbW : 0<bW) (hfixed : 64*bW^2≤Z^η)
    (x : Point ι) (hx : Valid x)
    (hleft : coordinates p x 0*coordinates p x 2*coordinates p x 4≤bW*Z^D)
    (hright : coordinates p x 0*coordinates p x 2*coordinates p x 5≤bW*Z^D)
    (hmass : windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p (erasePoint x))≠0) :
    Z^τ≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2 := by
  obtain ⟨k,hk,hhigh,hbounds⟩ := tail_mass_live_bounds p a b Z D m (4*η+τ) hZ (erasePoint x) hmass
  have hc := coordinates_pos p hp x hx
  have h₀ := (hbounds 0).1.le
  have h₁ := (hbounds 1).2.le
  have h₃ := (hbounds 3).1.le
  rw [sourceNorms_erase] at h₀ h₁ h₃
  have hh := InverseInitialHighFrequencyTail.actual_annulus_high_gate Z D m
    (exponent Z (k 0).val) (exponent Z (k 1).val) (exponent Z (k 3).val) η τ bW
    (coordinates p x 0) (coordinates p x 1) (coordinates p x 2)
    (coordinates p x 4) (coordinates p x 5) (coordinates p x 3)
    hZ.le hη hbW (hc 1) (hc 2) (hc 4) (hc 5) h₀ h₁ h₃ hleft hright hfixed hhigh.le
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
    rfl
  simpa [coordinates,physicalCoordinates,hn] using hh

end SevenEighths.InverseInitialDyadicTailBound

end

end OAI

end Source2818

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialDyadicTailBound.lean; sha256: 0cd7c25aa26870571444ac7ed114be0d9add700dfb5e90596940e4423f867660 -/
section Source2819
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicTailBound
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialDyadicAssembly InverseInitialProfile
open InverseInitialRetainedSupport InverseInitialHighFrequencyTail
local notation "O"=>ActualEisensteinCubic.O

theorem actual_high_mass_tail (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (weights : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖weights i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m η bW Γ B₁ B₂ : ℝ),
    1<Z → 0≤η → 0<bW → 64*bW^2≤Z^η →
    0≤Lcap → bW*Z^D≤Z^Lcap → -m≤Lcap → m-D≤Lcap →
    0≤Γ → 0≤B₁ → 0≤B₂ → (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    Function.support W₁⊆Set.Iic bW → Function.support W₂⊆Set.Iic bW →
    ∀ (pool : Finset ι) (S : Finset (Source (ι:=ι) 0)) (w : Source (ι:=ι) 0→ℂ),
    (∀x∈S,x.common⊆pool) → (∀x∈S,x.overlap⊆pool) →
    (∀x∈S,x.divisor⊆x.common) → (∀x∈S,x.frequency≠0) → (∀x∈S,‖w x‖≤Γ) →
    ∀ (a b : Fin 4→ℝ), (∀i,0<a i) → (∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) →
    ‖physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*(windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j (primeMark slots lists weights) W₁ W₂ Φ Z D m‖≤
      C*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨s,C,hC,hrapid⟩ := original_physical_tail_rapid Lcap saving τ hτ
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc hpr Ψ hΨ j slots lists weights hdis hwgt W₁ W₂ Φ
    Z D m η bW Γ B₁ B₂ hZ hη hbW hfixed hcap hsize hm hmd hΓ hB₁ hB₂ hW₁ hW₂ hs₁ hs₂
    pool S w hcommon hoverlap hdiv hfreq hw a b ha hrange
  let wt : Point ι→ℂ := ((fun x=>w x*(windowMass (tailWindows a b Z D m (4*η+τ))
    (sourceNorms p x):ℂ))∘erasePoint)
  let live (x : Point ι) : Prop := ∃ρ : SecondRayIndex,
    wt x*physicalTerm p hp hcop hg Ψ j (primeMark slots lists weights) W₁ W₂ Φ Z D m x ρ≠0
  let F := (pointSource pool S).filter live
  have hmem (x) (hx : x∈F) : x∈pointSource pool S := (Finset.mem_filter.mp hx).1
  have hvalid (x) (hx : x∈F) : Valid x := pointSource_valid pool S hdiv hfreq x (hmem x hx)
  have hold (x) (hx : x∈F) : erasePoint x∈S := pointSource_erase_mem pool S x (hmem x hx)
  have hgeometry (x) (hx : x∈F) :
      (coordinates p x 0≤bW*Z^D ∧ coordinates p x 1≤bW*Z^D ∧
       coordinates p x 2≤bW*Z^D ∧ coordinates p x 4≤bW*Z^D ∧ coordinates p x 5≤bW*Z^D) ∧
      (coordinates p x 0*coordinates p x 2*coordinates p x 4≤bW*Z^D ∧
       coordinates p x 0*coordinates p x 2*coordinates p x 5≤bW*Z^D) ∧
      windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p (erasePoint x))≠0 := by
    obtain ⟨ρ,hρ⟩ := (Finset.mem_filter.mp hx).2
    have hpterm := (mul_ne_zero_iff.mp hρ).2
    refine ⟨live_ideal_caps p hp hcop hg hpr Ψ j _ W₁ W₂ Φ Z D m bW
      (by linarith) hs₁ hs₂ x (hvalid x hx) ρ hpterm,
      live_whole_columns p hp hcop hg hpr Ψ j _ W₁ W₂ Φ Z D m bW
      (by linarith) hs₁ hs₂ x (hvalid x hx) ρ hpterm,?_⟩
    intro hz
    apply (mul_ne_zero_iff.mp hρ).1
    simp only [wt,Function.comp_apply,hz,Complex.ofReal_zero,mul_zero]
  have hn (x : Point ι) (i : Fin 5) := sourceKey_norm_coordinate p x i
  have hwhole (x) (hx : x∈F) :
      primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤bW*Z^D ∧
      primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤bW*Z^D := by
    have he := (hgeometry x hx).2.1
    have hn0 := hn x 0
    have hn2 := hn x 2
    have hn3 := hn x 3
    have hn4 := hn x 4
    simp [sourceKey,idealIndex] at hn0 hn2 hn3 hn4
    rw [←hn0,←hn2,←hn3,←hn4] at he
    exact he
  have hfilter := physicalBlock_filter_of_live p hp hcop hg (pointSource pool S) live wt Ψ j
    (primeMark slots lists weights) W₁ W₂ Φ Z D m (fun x hx ρ hn=>⟨ρ,hn⟩)
  change ‖physicalBlock p hp hcop hg (pointSource pool S) wt Ψ j _ W₁ W₂ Φ Z D m‖≤_
  rw [hfilter]
  have hr := hrapid p hp hcop hg hinj hc Ψ hΨ j slots lists weights hdis hwgt W₁ W₂ Φ
    Z D m (max 1 (bW*Z^D)) Γ B₁ B₂ hZ.le (le_max_left _ _) hcap
    (max_le (Real.one_le_rpow hZ.le hcap) hsize) hm hmd hΓ hB₁ hB₂ hW₁ hW₂ pool F wt hvalid
  suffices hbound : ‖physicalBlock p hp hcop hg F wt Ψ j (primeMark slots lists weights) W₁ W₂ Φ Z D m‖≤
      C*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) by
    have hset : @Finset.filter (Point ι) live (fun x=>Classical.propDecidable (live x))
        (pointSource pool S)=F := by
      ext x
      simp only [Finset.mem_filter,F]
    rw [hset]
    exact hbound
  refine hr ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact (mass_weight_bound p a b _ ha w (erasePoint x) (hrange _ (hold x hx))).trans (hw _ (hold x hx))
  · intro x hx
    exact pointSource_supports pool S hcommon hoverlap hdiv x (hmem x hx)
  · intro x hx i
    rw [sourceKey_norm_coordinate]
    have he := (hgeometry x hx).1
    apply le_trans _ (le_max_right 1 (bW*Z^D))
    fin_cases i
    · exact he.1
    · exact he.2.1
    · exact he.2.2.1
    · exact he.2.2.2.1
    · exact he.2.2.2.2
  · intro x hx
    exact (hwhole x hx).1.trans (le_max_right _ _)
  · intro x hx
    exact (hwhole x hx).2.trans (le_max_right _ _)
  · intro x hx
    exact live_mass_radial_gate p hp a b Z D m η τ bW hZ hη hbW hfixed x
      (hvalid x hx) (hgeometry x hx).2.1.1 (hgeometry x hx).2.1.2 (hgeometry x hx).2.2

end SevenEighths.InverseInitialDyadicTailBound

end

end OAI

end Source2819

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialProfileBounds.lean; sha256: 65e92ba49d40f033c568f6f7f86d3fcb15145c769dd504974072d78d231fca58 -/
section Source2820
namespace OAI

noncomputable section

open scoped Classical SchwartzMap
namespace SevenEighths.InverseInitialProfileBounds
open InverseInitialProfile InverseMoment FourierBridge

theorem clipped_norm (W:ℝ→ℂ)(c θ x:ℝ):‖clippedSource W c θ x‖=‖W (c*x)‖:=by
  simp only [clippedSource,norm_mul,logPhase_norm,one_mul]

theorem clipped_bound (W:ℝ→ℂ)(B:ℝ)(hW:∀x,‖W x‖≤B)(c θ x:ℝ):
    ‖clippedSource W c θ x‖≤B:=by rw [clipped_norm];exact hW _

theorem clipped_support (W:ℝ→ℂ)(a b c cmax θ:ℝ)(ha:0<a)(hc:1≤c)(hcm:c≤cmax)
    (hW:Function.support W⊆Set.Icc a b):
    Function.support (clippedSource W c θ)⊆Set.Icc (a/cmax) b:=by
  intro x hx
  have hn:W (c*x)≠0:=(mul_ne_zero_iff.mp hx).2
  have hs:=hW hn
  have hcp:0<c:=zero_lt_one.trans_le hc
  have hxpos:0<x:=pos_of_mul_pos_right (ha.trans_le hs.1) hcp.le
  constructor
  · apply (div_le_iff₀ (hcp.trans_le hcm)).mpr
    exact hs.1.trans (by nlinarith)
  · have hxc:x≤c*x:=le_mul_of_one_le_left hxpos.le hc
    exact hxc.trans hs.2

theorem clipped_support_upper (W:ℝ→ℂ)(a b c θ:ℝ)(ha:0<a)(hc:1≤c)
    (hW:Function.support W⊆Set.Icc a b):Function.support (clippedSource W c θ)⊆Set.Iic b:=
  fun _ hx=>(clipped_support W a b c c θ ha hc le_rfl hW hx).2

theorem childLogTest_eq_clipped (W:ℝ→ℂ)(θ:ℝ):childLogTest W θ=clippedSource W 1 θ:=by
  funext x
  simp only [childLogTest,clippedSource,mul_comm,mul_one]

theorem childLogTest_norm (W:ℝ→ℂ)(θ x:ℝ):‖childLogTest W θ x‖=‖W x‖:=by
  rw [childLogTest_eq_clipped,clipped_norm,one_mul]

end SevenEighths.InverseInitialProfileBounds

end

end OAI

end Source2820

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialFiniteEnergy.lean; sha256: e0b57769bb736d8609df3c58c893c2f14cf7cbfdad055044bb65f2f06ac00e35 -/
section Source2821
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialFiniteEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

theorem finite_physical_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (B₀:ℝ)(hB₀:0≤B₀)(hb₁:∀x,‖W₁ x‖≤B₀)(hb₂:∀x,‖W₂ x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
      (∀x∈S,x.common⊆Finset.univ)→(∀x∈S,x.overlap⊆Finset.univ)→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤c₁→c₁≤bcap→1≤c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ S) (w∘erasePoint) Ψ
        (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
        (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨J,Btree,hBtree,hretained⟩:=InverseInitialRetainedSum.retained_sum_bound
    W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ Φ
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  obtain ⟨ss,Ct,hCt,htail⟩:=InverseInitialDyadicTailBound.actual_high_mass_tail (2*cap+2) 1 τ hτ
  let tailC:=Ct*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have htailC:0≤tailC:=by dsimp [tailC];positivity
  have hevent:∀ᶠZ:ℝ in atTop,max 1 b₀≤Z ∧ 64*(max 1 b₀)^2≤Z^η:=
    (eventually_ge_atTop (max 1 b₀)).and
      ((tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (64*(max 1 b₀)^2)))
  obtain ⟨Zaux,haux⟩:=eventually_atTop.mp hevent
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨Cr,Zr,hCr,hZr,hretained⟩:=hretained q hq
  refine ⟨Cr+tailC,max Zr Zaux,by linarith,lt_max_of_lt_left hZr,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf hcommon hoverlap
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent
    c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  have hZr':Zr≤Z:=(le_max_left _ _).trans hZ
  have hZp:1<Z:=hZr.trans_le hZr'
  obtain ⟨hbZ,h64⟩:=haux Z ((le_max_right _ _).trans hZ)
  have hDcap:D≤cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq];linarith
  have hsize:max 1 b₀*Z^D≤Z^(2*cap+2):=by
    calc
      _≤Z*Z^D:=mul_le_mul_of_nonneg_right hbZ (Real.rpow_nonneg (by linarith) _)
      _=Z^(D+1):=by rw [Real.rpow_add (by linarith : 0<Z),Real.rpow_one];ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)
  have hs₁':Function.support (clippedSource W₁ c₁ θ₁)⊆Set.Iic (max 1 b₀):=
    by
      intro x hx
      exact le_trans (clipped_support_upper W₁ a₀ b₀ c₁ θ₁ ha₀ hc₁ hs₁ hx) (le_max_right 1 b₀)
  have hs₂':Function.support (clippedSource W₂ c₂ θ₂)⊆Set.Iic (max 1 b₀):=
    by
      intro x hx
      exact le_trans (clipped_support_upper W₂ a₀ b₀ c₂ θ₂ ha₀ hc₂ hs₂ hx) (le_max_right 1 b₀)
  obtain ⟨T,hT,hfreqcap⟩:=exists_source_frequency_cap p S
  have hsplit:=actual_physical_retained_tail p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ S hdiv hf w Ψ
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ
    Z D m (max 1 b₀) T (4*η+τ) hZp hs₁' hs₂' hfreqcap
  rw [hsplit]
  apply (norm_add_le _ _).trans
  have hret:=hretained Z hZr' Dpool hD all assigned hassigned hK lists Hslot coeff
    hdis hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf
    D m r T hm hT hprodj hprod hDeq hmargin₁ hmargin₂ hparent c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  let Sc:=cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)
  have ht:=htail p hp hcop hg (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (poolPrimary_odd F hFa) (InverseInitialRayAttachment.poolPrimary_primary F hFa) Ψ hΨ
    (assignedElement assigned qelem) (all\assigned) lists coeff
    (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hac
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m η (max 1 b₀) 1 B₀ B₀
    hZp hη.le (by positivity) h64 (by linarith) hsize (by linarith) (by linarith)
    (by norm_num) hB₀ hB₀ (clipped_bound W₁ B₀ hb₁ c₁ θ₁) (clipped_bound W₂ B₀ hb₂ c₂ θ₂)
    hs₁' hs₂' Finset.univ Sc w
    (fun x hx=>hcommon x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hoverlap x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hw x (Finset.mem_filter.mp hx).1)
    (fun _=>1) (physicalCaps (max 1 b₀) Z D T) (by intros;norm_num)
    (fun x hx=>(Finset.mem_filter.mp hx).2)
  have hheight:1≤((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg θ₁]))
      (one_le_pow₀ (by linarith [norm_nonneg θ₂]))
  have hpow:Z^(-1:ℝ)≤Z^(m+15*η+π+eps+loss):=
    Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)
  apply (add_le_add hret ht).trans
  change Cr*Z^(m+15*η+π+eps+loss)*_+(Ct*1*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-1:ℝ))≤_
  have hh:tailC*Z^(-1:ℝ)≤tailC*Z^(m+15*η+π+eps+loss)*
      ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=by
    calc
      _≤tailC*Z^(m+15*η+π+eps+loss):=mul_le_mul_of_nonneg_left hpow htailC
      _≤_:=le_mul_of_one_le_right (by positivity) hheight
  convert add_le_add_left hh (Cr*Z^(m+15*η+π+eps+loss)*
    ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))) using 1 <;> dsimp [tailC] <;> ring

end SevenEighths.InverseInitialFiniteEnergy

end

end OAI

end Source2821

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialPhysicalReassembly.lean; sha256: 4d02cad9a4c3eacbca11464807eae015a151e54a7e3b25ca3f5c0b43f3c5b98e -/
section Source2822
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialPhysicalReassembly
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem initialColumn_zero_common (Ψ:O→*ℂ)(j d h:O)(H:Finset ι→ℂ)
    (G U:Finset ι)(hd:¬Disjoint G U):
    initialColumn p hp hcop hg Ψ j (∏i∈G,p i) d h H U=0:=by
  obtain ⟨i,hiG,hiU⟩:=Finset.not_disjoint_iff.mp hd
  have hm:rowCoprimeMask (fun i=>Ideal.span {p i}) U (j*∏i∈G,p i)=0:=by
    have hh:∃i∈U,j*∏k∈G,p k∈Ideal.span {p i}:=
      ⟨i,hiU,Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hiG) j)⟩
    simp only [rowCoprimeMask,ite_eq_left hh]
  simp only [initialColumn,hm,mul_zero,zero_mul]

theorem physicalTerm_zero_left_common (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(G E V N M:Finset ι)(h:O)(ρ:SecondRayIndex)
    (hd:¬Disjoint G (V∪N)):
    physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ=0:=by
  simp only [physicalTerm,initialColumn_zero_common p hp hcop hg _ _ _ _ _ _ _ hd,
    star_zero,mul_zero,zero_mul]

theorem physicalTerm_zero_right_common (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(G E V N M:Finset ι)(h:O)(ρ:SecondRayIndex)
    (hd:¬Disjoint G (V∪M)):
    physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ=0:=by
  simp only [physicalTerm,initialColumn_zero_common p hp hcop hg _ _ _ _ _ _ _ hd,
    mul_zero,zero_mul]

private theorem missing_residual_common (pool G V N:Finset ι)
    (hN:N∈(pool\V).powerset)(hn:N∉((pool\G)\V).powerset):¬Disjoint G (V∪N):=by
  intro hd
  apply hn
  apply Finset.mem_powerset.mpr
  intro i hi
  have hh:=Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hi)
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hh.1,
    fun hG=>Finset.disjoint_left.mp hd hG (Finset.mem_union_right V hi)⟩,hh.2⟩

theorem rectangle_restore_common
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m:ℝ)(pool G E V:Finset ι)(h:O):
    (∑N∈((pool\G)\V).powerset,∑M∈((pool\G)\V).powerset,∑ρ:SecondRayIndex,
      physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ)=
    ∑N∈(pool\V).powerset,∑M∈(pool\V).powerset,∑ρ:SecondRayIndex,
      physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ:=by
  have hs:((pool\G)\V).powerset⊆(pool\V).powerset:=
    Finset.powerset_mono.mpr (Finset.sdiff_subset_sdiff Finset.sdiff_subset (Finset.Subset.refl _))
  calc
    _=∑N∈(pool\V).powerset,∑M∈((pool\G)\V).powerset,∑ρ:SecondRayIndex,
        physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ:=by
      apply Finset.sum_subset hs
      intro N hN hn
      apply Finset.sum_eq_zero
      intro M hM
      apply Finset.sum_eq_zero
      intro ρ hρ
      exact physicalTerm_zero_left_common p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m G E V N M h ρ
        (missing_residual_common pool G V N hN hn)
    _=_:=by
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_subset hs
      intro M hM hm
      apply Finset.sum_eq_zero
      intro ρ hρ
      exact physicalTerm_zero_right_common p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m G E V N M h ρ
        (missing_residual_common pool G V M hM hm)

def sourceCodes (pool:Finset ι)(T:Finset O):
    Finset (Σ _G:Finset ι,Σ _E:Finset ι,Finset ι×O):=
  pool.powerset.sigma (fun G=>G.powerset.sigma (fun _E=>(pool\G).powerset×ˢT))

def sourceOfCode (x:Σ _G:Finset ι,Σ _E:Finset ι,Finset ι×O):Source (ι:=ι) 0 where
  common:=x.1
  divisor:=x.2.1
  overlap:=x.2.2.1
  frequency:=x.2.2.2
  assigned:=Fin.elim0

omit [DecidableEq ι] in
theorem sourceOfCode_injective:Function.Injective (sourceOfCode (ι:=ι)):=by
  rintro ⟨G,E,V,h⟩ ⟨G',E',V',h'⟩ he
  have hG:=congrArg Source.common he
  have hE:=congrArg Source.divisor he
  have hV:=congrArg Source.overlap he
  have hh:=congrArg Source.frequency he
  dsimp only [sourceOfCode] at hG hE hV hh
  subst G';subst E';subst V';subst h'
  rfl

def finiteSource (pool:Finset ι)(T:Finset O):Finset (Source (ι:=ι) 0):=
  (sourceCodes pool T).image sourceOfCode

theorem finiteSource_sum {A:Type*}[AddCommMonoid A]
    (pool:Finset ι)(T:Finset O)(f:Source (ι:=ι) 0→A):
    (∑x∈finiteSource pool T,f x)=
      ∑G∈pool.powerset,∑E∈G.powerset,∑V∈(pool\G).powerset,∑h∈T,
        f ⟨G,E,V,h,Fin.elim0⟩:=by
  rw [finiteSource,Finset.sum_image (fun _ _ _ _ he=>sourceOfCode_injective he)]
  simp only [sourceCodes,Finset.sum_sigma,Finset.sum_product,sourceOfCode]

theorem mem_finiteSource (pool:Finset ι)(T:Finset O)(x:Source (ι:=ι) 0):
    x∈finiteSource pool T ↔ x.common⊆pool ∧ x.divisor⊆x.common ∧
      x.overlap⊆pool\x.common ∧ x.frequency∈T:=by
  constructor
  · intro hx
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    simpa only [sourceCodes,Finset.mem_sigma,Finset.mem_product,Finset.mem_powerset,
      sourceOfCode,and_assoc] using ha
  · rintro ⟨hG,hE,hV,hh⟩
    refine Finset.mem_image.mpr ⟨⟨x.common,x.divisor,x.overlap,x.frequency⟩,?_,?_⟩
    · simpa only [sourceCodes,Finset.mem_sigma,Finset.mem_product,Finset.mem_powerset]
        using And.intro hG (And.intro hE (And.intro hV hh))
    · apply Source.ext <;> try rfl
      funext i
      exact Fin.elim0 i

theorem finiteSource_divisor (pool:Finset ι)(T:Finset O):
    ∀x∈finiteSource pool T,x.divisor⊆x.common:=by
  intro x hx
  exact (mem_finiteSource pool T x).mp hx |>.2.1

theorem finiteSource_nonzero (pool:Finset ι)(T:Finset O)(hT:(0:O)∉T):
    ∀x∈finiteSource pool T,x.frequency≠0:=by
  intro x hx he
  exact hT (he ▸ ((mem_finiteSource pool T x).mp hx).2.2.2)

theorem finite_physical_reassembly
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (pool:Finset ι)(freqT:Finset O)(Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ):
    (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
      if Disjoint U T then ∑E∈G.powerset,∑h∈freqT,
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E h else 0)=
    physicalBlock p hp hcop hg (pointSource pool (finiteSource pool freqT))
      (fun _=>1) Ψ j σ (fun x=>star (W x)) W Φ Z D m:=by
  unfold physicalBlock
  rw [pointSource_sum,finiteSource_sum]
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro G hG
  have hif (U T:Finset ι):
      (if Disjoint U T then ∑E∈G.powerset,∑h∈freqT,
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E h else 0)=
      ∑E∈G.powerset,∑h∈freqT,if Disjoint U T then
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E h else 0:=by
    split_ifs <;> simp
  simp_rw [hif,Finset.sum_comm (s:=(pool\G).powerset) (t:=G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  simp_rw [Finset.sum_comm (s:=(pool\G).powerset) (t:=freqT)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [original_ray_common_insertion p hp hcop hg hinj]
  apply Finset.sum_congr rfl
  intro V hV
  exact rectangle_restore_common p hp hcop hg Ψ j σ (fun x=>star (W x)) W Φ Z D m pool G E V h

end SevenEighths.InverseInitialPhysicalReassembly

end

end OAI

end Source2822

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailInfinite.lean; sha256: a216c6ea8c2533bbf10200a7dc56400fce5e71cefc37e64055c32affac744fe7 -/
section Source2823
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O"=>ActualEisensteinCubic.O

theorem weighted_radial_summable (Φ : 𝓢(ℝ,ℂ)) (K Γ : ℝ) (hK : 0<K)
    (P : O→Prop) (a : O→ℂ) (ha : ∀h,P h→‖a h‖≤Γ) :
    Summable (fun h : {h:O // P h}=>a h.val*paperRadialFourier Φ (K*‖eisEmbedding h.val‖^2)) := by
  apply Summable.of_norm_bounded
    (((paperRadialFourier_lattice_summable_norm Φ K hK).subtype P).mul_left Γ)
  intro h
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ha h.val h.property) (norm_nonneg _)

theorem norm_tsum_of_finite_bound {α : Type*} (f : α→ℂ) (hf : Summable f) (B : ℝ)
    (hb : ∀F : Finset α,‖∑h∈F,f h‖≤B) : ‖∑'h,f h‖≤B := by
  exact le_of_tendsto hf.hasSum.norm (Filter.Eventually.of_forall hb)

theorem weighted_radial_tsum_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (Φ : 𝓢(ℝ,ℂ)) (K T Γ : ℝ), 0<K → 0≤T → 0≤Γ →
    ∀ (P : O→Prop) (a : O→ℂ),
    (∀h,P h→T≤K*‖eisEmbedding h‖^2) → (∀h,P h→‖a h‖≤Γ) →
    ‖∑'h : {h:O // P h},a h.val*paperRadialFourier Φ (K*‖eisEmbedding h.val‖^2)‖≤
      Γ*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/((min 1 K)^2*(1+T)^A) := by
  obtain ⟨s,C,hC,hbound⟩ := finite_radial_tail A
  refine ⟨s,C,hC,?_⟩
  intro Φ K T Γ hK hT hΓ P a htail ha
  apply norm_tsum_of_finite_bound _ (weighted_radial_summable Φ K Γ hK P a ha)
  intro F
  have hi : Function.Injective (fun h : {h:O // P h}=>h.val) := Subtype.val_injective
  have he : (∑h∈F,a h.val*paperRadialFourier Φ (K*‖eisEmbedding h.val‖^2))=
      ∑h∈F.image Subtype.val,a h*paperRadialFourier Φ (K*‖eisEmbedding h‖^2) := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ hh=>hi hh
  rw [he]
  apply hbound Φ K T Γ hK hT hΓ (F.image Subtype.val) a
  · intro h hh
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hh
    exact htail x.val x.property
  · intro h hh
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hh
    exact ha x.val x.property

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end Source2823

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialPhysicalLimit.lean; sha256: 857fb5ad01429b0d61de212c092d3f6bfa7a1334d9cb2b8a3f17338acd4ca686 -/
section Source2824
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialPhysicalLimit
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialPhysicalReassembly
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def physicalFrequency (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(h:O):ℂ:=
  ∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
    if Disjoint U T then ∑E∈G.powerset,
      initialPhysicalMode p hp hcop hg Ψ j marks W Φ Z D m G U T E h else 0

theorem physicalFrequency_finite
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (pool:Finset ι)(freqT:Finset O)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ):
    (∑h∈freqT,physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h)=
    physicalBlock p hp hcop hg (pointSource pool (finiteSource pool freqT))
      (fun _=>1) Ψ j marks (fun x=>star (W x)) W Φ Z D m:=by
  rw [←finite_physical_reassembly p hp hcop hg hinj]
  unfold physicalFrequency
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd:Disjoint U T
  · simp only [hd,ite_true]
    exact Finset.sum_comm
  · simp only [hd,ite_false,Finset.sum_const_zero]

theorem physicalFrequency_hasSum
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:0<Z):
    HasSum (physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m)
      (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
        if Disjoint U T then ∑E∈G.powerset,∑'h:O,
          initialPhysicalMode p hp hcop hg Ψ j marks W Φ Z D m G U T E h else 0):=by
  unfold physicalFrequency
  apply hasSum_sum
  intro G hG
  apply hasSum_sum
  intro U hU
  apply hasSum_sum
  intro T hT
  by_cases hd:Disjoint U T
  · simp only [hd,ite_true]
    apply hasSum_sum
    intro E hE
    exact (initialPhysicalMode_summable p hp hcop hg hinj hc hpr Ψ j marks W Φ hZ D m
      G U T E
      (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hU) Finset.disjoint_sdiff)
      (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff) hd).hasSum
  · simpa only [hd,ite_false] using (hasSum_zero : HasSum (fun _ : O=>(0:ℂ)) 0)

theorem original_input_zero_nonzero
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:0<Z):
    (∑'u:O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg pool Ψ j 1 1
        (initialTest p marks W Z D) u‖^2:ℝ))=
    physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m 0+
      ∑'h:O,if h=0 then 0 else physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h:=by
  rw [initial_input_physical p hp hcop hg hinj hc hpr pool Ψ j marks W Φ hZ D m]
  have hs:=physicalFrequency_hasSum p hp hcop hg hinj hc hpr pool Ψ j marks W Φ Z D m hZ
  rw [←hs.tsum_eq]
  exact hs.summable.tsum_eq_add_tsum_ite 0

theorem nonzero_frequency_norm_le
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m B:ℝ)(hZ:0<Z)
    (hfinite:∀freqT:Finset O,(0:O)∉freqT→
      ‖physicalBlock p hp hcop hg (pointSource pool (finiteSource pool freqT))
        (fun _=>1) Ψ j marks (fun x=>star (W x)) W Φ Z D m‖≤B):
    ‖∑'h:O,if h=0 then 0 else physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h‖≤B:=by
  have hs:=physicalFrequency_hasSum p hp hcop hg hinj hc hpr pool Ψ j marks W Φ Z D m hZ
  have hs0:Summable (fun h:O=>if h=0 then (0:ℂ) else
      physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h):=by
    apply (hs.summable.indicator {h:O|h≠0}).congr
    intro h
    by_cases he:h=0 <;> simp [Set.indicator,he]
  apply InverseInitialHighFrequencyTail.norm_tsum_of_finite_bound _ hs0
  intro T
  let freqT:=T.filter (fun h:O=>h≠0)
  have hzero:(0:O)∉freqT:=by simp [freqT]
  have he:(∑h∈T,if h=0 then (0:ℂ) else physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h)=
      ∑h∈freqT,physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h:=by
    simp only [freqT,Finset.sum_filter,ite_not]
  rw [he,physicalFrequency_finite p hp hcop hg hinj]
  exact hfinite freqT hzero

end SevenEighths.InverseInitialPhysicalLimit

end

end OAI

end Source2824

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialZeroMode.lean; sha256: d1da201983ac351b91873c17f9408fc27e33edd0627483ffdd3a8f549ae54504 -/
section Source2825
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialZeroMode
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT EisensteinSchwartzPoisson InverseMoment
open InverseInitialRayAttachment
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda

theorem marked_coefficient_mass (eps b B:ℝ)(heps:0<eps)(hb:0<b)(_hB:0≤B):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,λ₀∉Ideal.span {p i})(_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(m c d:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤B)→(∀x,W x≠0→x≤b)→∀X:ℝ,0<X→
      (∑A∈pool.powerset,‖secondInputCoefficient p hg Ψ m c d
        (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) A‖^2)≤C*X^(1+eps) := by
  obtain ⟨Cm,hCm,hm⟩:=finite_primeMark_small_power (eps/2) (by positivity)
  refine ⟨128*b*(Cm*b^(eps/2)*B)^2+1,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj pool Ψ hΨ m c d slots lists a hdis ha W hW hs X hX
  let T:=pool.powerset.filter (fun A=>W (primeProductNorm p A/X)≠0)
  have hXb:0<b*X:=mul_pos hb hX
  have hnorm:∀A∈T,primeProductNorm p A≤b*X:=by
    intro A hA
    exact (div_le_iff₀ hX).mp (hs _ (Finset.mem_filter.mp hA).2)
  have hcard:(T.card:ℝ)≤128*(b*X):=by
    by_cases hsmall:1≤b*X
    · apply (Nat.cast_le.mpr (Finset.card_le_card (show T⊆boundedPrimeSupports p pool (b*X) from ?_))).trans
        (boundedPrimeSupports_card p hinj pool (b*X) hsmall)
      intro A hA
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1,hnorm A hA⟩
    · have hz:T=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro A hA
        exact hsmall ((primeProductNorm_ge_one p hp A).trans (hnorm A hA))
      rw [hz]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  have he:(∑A∈pool.powerset,‖secondInputCoefficient p hg Ψ m c d
      (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) A‖^2)=
      ∑A∈T,‖secondInputCoefficient p hg Ψ m c d
        (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) A‖^2:=by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro A hA hn
    have hz:W (primeProductNorm p A/X)=0:=by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hA,hh⟩)
    simp only [secondInputCoefficient,hz,mul_zero,norm_zero,zero_pow (by decide:2≠0)]
  have hcoeff:∀A∈T,‖secondInputCoefficient p hg Ψ m c d
      (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) A‖≤Cm*(b*X)^(eps/2)*B:=by
    intro A hA
    apply (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d _ A).trans
    rw [norm_mul]
    apply mul_le_mul _ (hW _) (norm_nonneg _) (by positivity)
    exact (hm p hp hcop slots lists a hdis ha A).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (primeProductNorm_pos p hp A).le (hnorm A hA) (by positivity)) hCm.le)
  rw [he]
  calc
    _≤∑_A∈T,(Cm*(b*X)^(eps/2)*B)^2:=by
      apply Finset.sum_le_sum
      intro A hA
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoeff A hA) 2
    _=(T.card:ℝ)*(Cm*(b*X)^(eps/2)*B)^2:=by simp
    _≤(128*(b*X))*(Cm*(b*X)^(eps/2)*B)^2:=mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _=(128*b*(Cm*b^(eps/2)*B)^2)*X^(1+eps):=by
      rw [Real.mul_rpow hb.le hX.le,Real.rpow_add hX,Real.rpow_one]
      have hh:(X^(eps/2))^2=X^eps:=by
        rw [←Real.rpow_natCast,←Real.rpow_mul hX.le]
        congr 1
        norm_num
      calc
        _=(128*b*(Cm*b^(eps/2)*B)^2)*(X*(X^(eps/2))^2):=by ring
        _=_:=by rw [hh]
    _≤_:=by nlinarith [Real.rpow_nonneg hX.le (1+eps)]

theorem marked_normalized_zero (eps b B:ℝ)(heps:0<eps)(hb:0<b)(hB:0≤B)
    (Φ:𝓢(ℝ,ℂ)):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,λ₀∉Ideal.span {p i})(_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(m c d:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤B)→(∀x,W x≠0→x≤b)→∀X Y:ℝ,0<X→0<Y→
      ∀K:Finset ι→Finset ι→Finset O,
      (∀G∈pool.powerset,∀E∈G.powerset,(0:O)∈K G E)→
      ‖(X⁻¹:ℂ)*truncatedSecondZero p hg pool Ψ m c d
        (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) Φ Y K‖≤C*Y*X^eps := by
  obtain ⟨Cm,hCm,hm⟩:=marked_coefficient_mass eps b B heps hb hB
  refine ⟨Cm*‖paperRadialFourier Φ 0‖+1,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj pool Ψ hΨ m c d slots lists a hdis ha W hW hs X Y hX hY K hK
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX]
  have hz:=truncatedSecondZero_norm_le p hg hinj pool Ψ m c d
    (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) Φ Y K hK
  rw [abs_of_pos hY] at hz
  apply (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hX.le)).trans
  have hm':=hm p hp hcop hg hinj pool Ψ hΨ m c d slots lists a hdis ha W hW hs X hX
  calc
    _≤X⁻¹*(Y*‖paperRadialFourier Φ 0‖*(Cm*X^(1+eps))):=by gcongr
    _=(Cm*‖paperRadialFourier Φ 0‖)*Y*X^eps:=by
      rw [Real.rpow_add hX,Real.rpow_one]
      field_simp
    _≤_:=by nlinarith [mul_nonneg hY.le (Real.rpow_nonneg hX.le eps)]

end SevenEighths.InverseInitialZeroMode

end

end OAI

end Source2825

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialZeroModePhysical.lean; sha256: fdd4e2d3ee2d735f6383bda24f24a34f1a5400cd88cb4d879a10a7708c541311 -/
section Source2826
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialZeroMode
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT EisensteinSchwartzPoisson InverseMoment
open InverseInitialRayAttachment FirstCauchyArithmetic
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,λ₀∉Ideal.span {p i})(hinj:Function.Injective (fun i=>Ideal.span {p i}))
  (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(hpr:∀i,λ₀^2∣p i-1)

include hinj hc hpr

theorem physical_zero_off_diagonal
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (G U T E:Finset ι)(hGU:Disjoint G U)(hGT:Disjoint G T)(hUT:Disjoint U T)(hne:U≠T):
    initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E 0=0 := by
  rw [←normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m
    G U T E hGU hGT hUT 0,
    activeGaussRowFactor_zero_of_ne p hp hg hinj T U hne.symm]
  simp

theorem physical_zero_empty
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (G E:Finset ι):
    initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G ∅ ∅ E 0=
    ((Z^(-D):ℝ):ℂ)*(Z^m:ℝ)*paperRadialFourier Φ 0*
      ((‖secondInputCoefficient p hg Ψ j 1 1 (fun _=>1) G‖^2:ℝ):ℂ)*
      star (initialTest p σ W Z D G)*initialTest p σ W Z D G*
      ((UniqueFactorizationMonoid.moebius (∏i∈E,Ideal.span {p i}):ℂ)/
        (‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)‖^2:ℝ)) := by
  rw [←normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m
    G ∅ ∅ E (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) (Finset.disjoint_empty_left _) 0,
    activeGaussRowFactor_empty (p := p) (hp := hp) (hg := hg) (hinj := hinj)]
  have hcoef (H:Finset ι→ℂ):secondInputCoefficient p hg Ψ j 1 1 H ∅=H ∅:=by
    simp [secondInputCoefficient,rowCoprimeMask,finiteSquarefreeRow]
  have hμ:supportMobius (fun i=>Ideal.span {p i}) ∅=(1:ℂ):=by
    change (UniqueFactorizationMonoid.moebius (1:Ideal O):ℂ)=1
    exact_mod_cast UniqueFactorizationMonoid.moebius_one
  simp only [overlapPairWeight,hcoef,hμ,one_mul,Finset.union_empty]
  have hempty:activeSupport (∅:Finset ι) ∅=∅:=by simp [activeSupport]
  let:IsEmpty (activeSupport (∅:Finset ι) ∅):=⟨fun ⟨x,hx⟩=>by
    simp only [activeSupport,Finset.sdiff_self,Finset.union_self,Finset.notMem_empty] at hx⟩
  simp only [Fintype.prod_empty,map_one,norm_one,Complex.ofReal_one,div_one,map_zero,norm_zero,
    zero_pow (by decide:2≠0),mul_zero,zero_div,mul_one]
  ring

theorem physical_zero_sum
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ):
    (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
      if Disjoint U T then ∑E∈G.powerset,
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E 0 else 0)=
      ((Z^(-D):ℝ):ℂ)*truncatedSecondZero p hg pool Ψ j 1 1
        (initialTest p σ W Z D) Φ (Z^m) (fun _ _=>{0}) := by
  unfold truncatedSecondZero
  simp only [Finset.mem_singleton,ite_true,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single ∅]
    · simp only [Finset.disjoint_empty_left,ite_true]
      rw [←Finset.sum_coe_sort (s:=G.powerset) (f:=fun E=>
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G ∅ ∅ E 0)]
      apply Finset.sum_congr rfl
      intro E hE
      rw [physical_zero_empty p hp hcop hg hinj hc hpr]
      ring
    · intro T hT hne
      simp only [Finset.disjoint_empty_left,ite_true]
      apply Finset.sum_eq_zero
      intro E hE
      exact physical_zero_off_diagonal p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m G ∅ T E
        (Finset.disjoint_empty_right _) (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff)
        (Finset.disjoint_empty_left _) hne.symm
    · simp
  · intro U hU hne
    apply Finset.sum_eq_zero
    intro T hT
    split_ifs with hUT
    · apply Finset.sum_eq_zero
      intro E hE
      have hneq:U≠T:=by
        intro he
        subst T
        exact hne (by simpa using Finset.disjoint_iff_inter_eq_empty.mp hUT)
      exact physical_zero_off_diagonal p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m G U T E
        (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hU) Finset.disjoint_sdiff)
        (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff) hUT hneq
    · rfl
  · simp

end SevenEighths.InverseInitialZeroMode

end

end OAI

end Source2826

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialZeroModeBudget.lean; sha256: af553ecdeb32913e43f759957474a83363807ed26f8ea9a2c331305c03ae0e2e -/
section Source2827
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialZeroMode
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT EisensteinSchwartzPoisson InverseMoment
open InverseInitialRayAttachment
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda

theorem physical_marked_zero_bound (loss L b B:ℝ)(hloss:0<loss)(hL:0≤L)
    (hb:0<b)(hB:0≤B)(Φ:𝓢(ℝ,ℂ)):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,λ₀∉Ideal.span {p i})(_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(_hpr:∀i,λ₀^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(j:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤B)→(∀x,W x≠0→x≤b)→
      ∀Z D m:ℝ,1≤Z→D≤L→
      ‖∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
        if Disjoint U T then ∑E∈G.powerset,
          initialPhysicalMode p hp hcop hg Ψ j (primeMark slots lists a)
            W Φ Z D m G U T E 0 else 0‖≤C*Z^(m+loss) := by
  let eps:=loss/(L+1)
  have heps:0<eps:=div_pos hloss (by linarith)
  obtain ⟨C,hC,hbound⟩:=marked_normalized_zero eps b B heps hb hB Φ
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc hpr pool Ψ hΨ j slots lists a hdis ha W hW hs Z D m hZ hD
  have hZ0:0<Z:=lt_of_lt_of_le zero_lt_one hZ
  rw [physical_zero_sum p hp hcop hg hinj hc hpr]
  have heq:((Z^(-D):ℝ):ℂ)=((Z^D:ℝ):ℂ)⁻¹:=by
    rw [Real.rpow_neg hZ0.le,Complex.ofReal_inv]
  rw [heq]
  have hb':=hbound p hp hcop hg hinj pool Ψ hΨ j 1 1 slots lists a hdis ha
    W hW hs (Z^D) (Z^m) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    (fun _ _=>{0}) (by intros; simp)
  change ‖_‖≤C*Z^(m+loss)
  apply hb'.trans
  rw [←Real.rpow_mul hZ0.le, mul_assoc,←Real.rpow_add hZ0]
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ ?_) hC.le
  have hprod:D*eps≤loss:=by
    apply (mul_le_mul_of_nonneg_right hD heps.le).trans
    dsimp [eps]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith:0<L+1)).mpr
    nlinarith
  linarith

end SevenEighths.InverseInitialZeroMode

end

end OAI

end Source2827

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialTotalEnergy.lean; sha256: 0ef6f457da3645cb613558815ec6f7d43e41ea445ede4a077bf0bea78e8c2e66 -/
section Source2828
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialTotalEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
theorem original_input_bound
    (W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(c θ:ℝ),1≤c→c≤bcap→
      ‖∑'u:O,Φ (‖eisEmbedding u‖^2/Z^m)*
        (‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) lists coeff)
            (clippedSource W c θ) Z D) u‖^2:ℝ)‖≤
        C*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*degree)) := by
  have hsstar:Function.support (fun x=>star (W x))⊆Set.Icc a₀ b₀:=by
    intro x hx
    apply hs
    simpa only [Function.mem_support,star_ne_zero] using hx
  have hbStar:∀x,‖star (W x)‖≤B₀:=by intro x;simpa only [norm_star] using hb x
  obtain ⟨J,Btree,hBtree,hfinite⟩:=InverseInitialFiniteEnergy.finite_physical_bound
    (fun x=>star (W x)) W a₀ b₀ bcap ha₀ hbcap hsstar hs
    (Complex.conjCLE.contDiff.comp hW) hW Φ B₀ hB₀ hbStar hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  obtain ⟨Cz,hCz,hzero⟩:=InverseInitialZeroMode.physical_marked_zero_bound
    loss cap (max 1 b₀) B₀ hloss hcap (by positivity) hB₀ Φ
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨Cf,Z₀,hCf,hZ₀,hfinite⟩:=hfinite q hq
  refine ⟨Cf+Cz,Z₀,by linarith,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent c θ hc hbc
  have hZp:1<Z:=hZ₀.trans_le hZ
  have hDcap:D≤cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq];linarith
  have hconj:(fun x=>star (clippedSource W c θ x))=clippedSource (fun x=>star (W x)) c (-θ):=
    funext (clippedSource_conjugate W c θ)
  have hn:=nonzero_frequency_norm_le p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_injective F hFa) (poolPrimary_odd F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ Ψ
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
    (clippedSource W c θ) Φ Z D m
    (Cf*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J)))
    (by linarith : 0<Z) (by
      intro freqT hzero
      rw [hconj]
      have h:=hfinite Z hZ Dpool hD all assigned hassigned hK lists Hslot coeff
        hdis hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
        (finiteSource Finset.univ freqT)
        (finiteSource_divisor Finset.univ freqT) (finiteSource_nonzero Finset.univ freqT hzero)
        (fun x hx=>Finset.subset_univ _) (fun x hx=>Finset.subset_univ _)
        D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent
        c c (-θ) θ hc hbc hc hbc (fun _=>1) (by intros;norm_num)
      simpa only [Function.comp_def,norm_neg,pow_mul,pow_two,mul_pow] using h)
  have hz0:=hzero p hp hcop hg (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (poolPrimary_odd F hFa) (InverseInitialRayAttachment.poolPrimary_primary F hFa)
    Finset.univ Ψ hΨ (assignedElement assigned qelem) (all\assigned) lists coeff
    (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hac
    (clippedSource W c θ) (clipped_bound W B₀ hb c θ)
    (fun x hx=>le_trans (clipped_support_upper W a₀ b₀ c θ ha₀ hc hs hx) (le_max_right 1 b₀))
    Z D m hZp.le hDcap
  rw [original_input_zero_nonzero p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_injective F hFa) (poolPrimary_odd F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ Ψ
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
    (clippedSource W c θ) Φ Z D m (by linarith)]
  apply (norm_add_le _ _).trans
  have hh:1≤(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J)):=one_le_pow₀ (by linarith [norm_nonneg θ])
  have hz1:Cz*Z^(m+loss)≤Cz*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J)):=by
    calc
      _≤Cz*Z^(m+15*η+π+eps+loss):=mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)) hCz.le
      _≤_:=le_mul_of_one_le_right (by positivity) hh
  change ‖physicalFrequency _ _ _ _ _ _ _ _ _ _ _ _ _ 0‖+_≤_
  exact (add_le_add (hz0.trans hz1) hn).trans_eq (by ring)

end SevenEighths.InverseInitialTotalEnergy

end

end OAI

end Source2828

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawInputBound.lean; sha256: 52f0a30ffcc67c68da206d8a001f52da24f53f04010c72e190402f8c75f3bc18 -/
section Source2829
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawInputBound
open ConcretePrimeRowBridge ActualEisensteinCubic ConcreteTraceCRT CompletedGauss SecondPassArithmetic CanonicalQuadraticSieve CanonicalRowCompletion
open CanonicalCoefficientClass InverseMoment InverseInitialProfile InverseInitialRayAttachment
open InverseInitialQuotientGeometry InverseInitialProfileBounds
local notation "O"=>ActualEisensteinCubic.O

theorem raw_input_bound
    (W:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support W⊆Set.Icc a b)
    (Φ:𝓢(ℝ,ℂ))(gap eps π η τ loss:ℝ)
    (hgap:0<gap)(heps:0<eps)(hπ:0<π)(hη:0<η)(hηone:η≤1)
    (hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss):
    ∃J:ℕ,∃Btree:ℝ,1≤Btree ∧ ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^3≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hg:=poolPrimary_good F hF;
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀ (r t : ℝ), (-2 : ℝ) ≤ r → r ≤ 1 - 2 * gap → 2 * r ≤ 3 - 2 * gap → r + 7 * η ≤ 2 →
    ‖∑'u:O,Φ (‖eisEmbedding u‖^2/Z)*
      (‖((Z^(-r/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ 1 1 1
        (initialTest p (fun _=>1) (childLogTest W t) Z r) u‖^2:ℝ)‖≤
      C*Z^(1+15*η+π+eps+loss)*(1+‖t‖)^(2*J) := by
  have hB:0≤SchwartzMap.seminorm ℝ 0 0 W:=apply_nonneg _ _
  have hb:∀x,‖W x‖≤SchwartzMap.seminorm ℝ 0 0 W:=fun x=>by
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using W.le_seminorm ℝ 0 0 x
  obtain ⟨degree,Btree,hBtree,hbound⟩:=InverseInitialTotalEnergy.original_input_bound
    W a b 1 ha le_rfl hs (W.smooth ⊤) Φ _ hB hb 2 gap eps π η τ loss
    (by norm_num) hgap heps hπ hη hηone hηsmall hτ hτsmall hloss 0
  refine ⟨InverseClippingProfiles.momentOrder (4*degree),Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,hbound⟩:=hbound q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hpool F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  intro p hg Ψ hΨ hperiod r t hrlo hr₁ hr₂ hrcap
  have hZp:1<Z:=hZ₀.trans_le hZ
  have hpool':Btree*Z^((2:ℝ)+1)≤Dpool:=by norm_num;exact hpool
  have hp:=Real.one_le_rpow hZp.le hη.le
  have h:=hbound Z hZ Dpool hpool' (σ:=Fin 0) ∅ ∅ (by simp) (by simp)
    (fun _=>∅) (fun _=>1) (fun _ _=>0) (by simp) (by simp) (by simp) (by simp)
    (fun _=>1) (fun _=>0) (fun _=>1) (fun _=>1) (fun _ _=>0)
    (by simp) (by simp) (by simp) (by simp) Ψ hΨ hperiod r 1 r
    (by norm_num) (by norm_num) hrlo (by simpa using hp) (by simpa [assignedCenter] using hp)
    (by simp [assignedCenter]) (by simpa [assignedCenter] using hr₁)
    (by simpa [assignedCenter] using hr₂) (by simpa [assignedCenter] using hrcap)
    1 t le_rfl le_rfl
  simp only [Finset.sdiff_self,assignedElement,Finset.prod_empty] at h
  have hemark : primeMark (∅:Finset (Fin 0)) (fun _=> (∅:Finset (primePool F)))
      (fun _ _=> (0:ℂ))=(fun _=>1) := by
    funext A
    exact primeMark_empty _ _ A
  rw [hemark] at h
  simpa only [
    Real.rpow_one,←childLogTest_eq_clipped] using h

end SevenEighths.DetectorDictionaryInverseRawInputBound

end

end OAI

end Source2829

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawGeometry.lean; sha256: 7ba7f551e6e4353798853bd092779ea5c10a961fbac9a7ba62c274b56d10b70c -/
section Source2830
namespace OAI

noncomputable section
namespace SevenEighths.DetectorDictionaryInverseRawGeometry
open InverseMoment InverseInitialCanonicalState

def capacityGap (c : ℝ) : ℝ:=c/(1+c)

theorem capacityGap_pos (c : ℝ) (hc : 0<c) : 0<capacityGap c :=
  div_pos hc (by linarith)

theorem capacityGap_lt_one (c : ℝ) (hc : 0<c) : capacityGap c<1 := by
  apply (div_lt_one (by linarith : 0<1+c)).mpr
  linarith

theorem raw_log_capacity (H D c : ℝ) (hH : 1<H) (hD : 1≤D) (hc : 0<c)
    (hcap : D^(1+c)≤H) :
    0≤Real.logb H D ∧ Real.logb H D≤1-capacityGap c ∧
    2*Real.logb H D≤3-capacityGap c ∧ H^(Real.logb H D)=D := by
  have hHp : 0<H:=zero_lt_one.trans hH
  have hDp : 0<D:=zero_lt_one.trans_le hD
  have hlogH : 0<Real.log H:=Real.log_pos hH
  have hh:=Real.log_le_log (Real.rpow_pos_of_pos hDp (1+c)) hcap
  rw [Real.log_rpow hDp] at hh
  have hr : Real.logb H D≤1/(1+c) := by
    unfold Real.logb
    apply (le_div_iff₀ (by linarith : 0<1+c)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hlogH).mpr
    simpa only [mul_div_assoc,mul_comm,mul_left_comm,one_mul] using hh
  have he : 1/(1+c)=1-capacityGap c := by
    unfold capacityGap
    field_simp
    ring
  have hg:=(capacityGap_pos c hc).le
  exact ⟨div_nonneg (Real.log_nonneg hD) hlogH.le,hr.trans_eq he,
    by linarith [hr.trans_eq he],Real.rpow_logb hHp (ne_of_gt hH) hDp⟩

theorem raw_fixed_reserves (c κ : ℝ) (hc : 0<c) (hκ : 0<κ) :
    ∃η τ π ε : ℝ,0<η ∧ 0<τ ∧ 0<π ∧ 0<ε ∧
      η≤1 ∧ η≤capacityGap c/200 ∧ τ≤capacityGap c/200 ∧
      40*η+π+ε≤κ := by
  let η:=min (capacityGap c/200) (min (κ/100) (1/100))
  have hg:=capacityGap_pos c hc
  have hη : 0<η:=lt_min (by positivity)
    (lt_min (by positivity) (by norm_num))
  have hηg : η≤capacityGap c/200:=min_le_left _ _
  have hηκ : η≤κ/100:=(min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η≤1/100:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η,η,κ/4,κ/4,hη,hη,by positivity,by positivity,by linarith,hηg,hηg,?_⟩
  linarith

theorem raw_retained_margins (H D c B θ v Hfreq η τ Q : ℝ)
    (hH : 1<H) (hD : 1≤D) (hc : 0<c) (hcap : D^(1+c)≤H)
    (hP : -2*η≤B-θ) (hQ : Q≤B-θ+3*η) (hη : 0≤η)
    (hηsmall : η≤capacityGap c/100) (hτ : τ≤capacityGap c/100)
    (hcut : InverseInitialProfile.radialCenter 1 Hfreq θ (Real.logb H D) B≤4*η+τ) :
    CanonicalMargins
      (max 0 (Real.logb H D-B-v)+(θ+v+2*η)) (θ+Hfreq+2*η) Q 0
      (3*capacityGap c/4) := by
  obtain ⟨hr,hfirst,hsecond,_⟩:=raw_log_capacity H D c hH hD hc hcap
  have hh:=enlarged_initial_margins 1 (Real.logb H D) 0 0 B θ v Hfreq η τ Q
    (capacityGap c) (capacityGap c)
    (by simpa using hfirst) (by simpa using hsecond) (by norm_num) hP
    (by simpa using hQ) (by simpa using (capacityGap_pos c hc).le) hη
    (by simpa using hηsmall) (by simpa using hτ) (by simpa using hcut)
  simpa using hh

theorem raw_output_budget (H D κ e : ℝ) (hH : 1≤H) (hκ : 0≤κ) (he : e≤κ) :
    H^(1+e)≤H*(H*max 1 D)^κ := by
  have hHp : 0<H:=zero_lt_one.trans_le hH
  rw [Real.rpow_add hHp,Real.rpow_one]
  apply mul_le_mul_of_nonneg_left _ hHp.le
  calc
    H^e≤H^κ:=Real.rpow_le_rpow_of_exponent_le hH he
    _≤(H*max 1 D)^κ:=Real.rpow_le_rpow hHp.le (by nlinarith [le_max_left 1 D]) hκ

end SevenEighths.DetectorDictionaryInverseRawGeometry

end

end OAI

end Source2830

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialRawDictionary.lean; sha256: 105bd240eb1ab8d0afaeb953710d51124ab6fffa8e56027970aaee372169dc77 -/
section Source2831
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialRawDictionary
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeRowClosure
open InverseInitialPoissonBridge InverseInitialConjugateEnergy
open ConcretePrimeRowBridge CompletedGauss UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def twistedProfile (W : ℝ → ℂ) (σ freq : ℝ) (x : ℝ) : ℂ :=
  W x*(x:ℂ)^(-shift σ freq)

theorem finite_source_cover (W : ℝ → ℂ) (D b : ℝ) (hD : 0<D)
    (hW : ∀x,W x≠0 → x≤b) (I : Ideal O) (hI : I≠0)
    (hi : W ((I.absNorm:ℝ)/D)≠0) : I∈idealsUpTo ⌈D*b⌉₊ := by
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩
  have hb := (div_le_iff₀ hD).mp (hW _ hi)
  have hn : (I.absNorm:ℝ)≤(⌈D*b⌉₊:ℝ) := by
    calc
      (I.absNorm:ℝ)≤D*b := by simpa only [mul_comm] using hb
      _≤(⌈D*b⌉₊:ℝ) := Nat.le_ceil _
  exact_mod_cast hn

theorem normalization_eq (Z r : ℝ) (hZ : 0<Z) :
    ((Z^r:ℝ):ℂ)^(-(1/2:ℂ))=((Z^(-r/2):ℝ):ℂ) := by
  have he : (-(1/2:ℂ))=((-(1/2:ℝ)):ℂ) := by norm_num
  calc
    _ = (((Z^r)^(-(1/2:ℝ)):ℝ):ℂ) := by
      simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,
        Complex.ofReal_ofNat] using (Complex.ofReal_cpow
          (Real.rpow_nonneg hZ.le r) (-(1/2:ℝ))).symm
    _ = _ := ?_
  rw [←Real.rpow_mul hZ.le]
  congr 2
  ring

theorem inverse_eq_initial_source (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ → ℂ) (Z r σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hcover : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq=
      originalTotalPolynomial S 1 η (fun _=>1)
        (twistedProfile W σ freq) Z r 0 u := by
  rw [polynomial_eq_finite χ true W (Z^r) σ freq S hcover,normalization_eq Z r hZ]
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one]
  apply congrArg (fun x:ℂ=>((Z^(-r/2):ℝ):ℂ)*x)
  apply Finset.sum_congr rfl
  intro I hI
  simp only [coefficient,ite_true,hrow,heckeIdealCharacter_apply,
    twistedProfile]
  ring

theorem canonical_inverse_eq_initial_source (η χ : Character) (m f z : O)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ → ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    polynomial χ true W (Z^r) σ freq=
      originalTotalPolynomial (idealsUpTo ⌈Z^r*b⌉₊) 1
        (idealCoeff η).toMonoidHom (fun _=>1)
        (twistedProfile W σ freq) Z r 0 (m^6*f^4*z) := by
  apply inverse_eq_initial_source (idealCoeff η).toMonoidHom χ (m^6*f^4*z)
    (HeckeRowClosure.idealCoeff_eq_row η χ m f z hrow) W Z r σ freq hZ
  exact finite_source_cover W (Z^r) b (Real.rpow_pos_of_pos hZ r) hW

theorem inverse_times_mark_eq_initial (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ → ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z)
    (S P : Finset (Ideal O)) (A : Ideal O → ℂ)
    (hcover : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑p∈P,A p*idealCoeff χ p)=
      ∑p∈P,A p*originalTotalPolynomial S p η
        (fun _=>1) (twistedProfile W σ freq) Z r z u := by
  rw [inverse_eq_initial_source η χ u hrow W Z r σ freq hZ S hcover]
  have hn : ((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ)=
      ((Z^(-(r+z)/2):ℝ):ℂ) := by
    rw [←Complex.ofReal_mul,←Real.rpow_add hZ]
    congr 2
    ring
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro I hI
  rw [hrow p]
  simp only [heckeIdealCharacter_apply]
  calc
    _ = (((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ))*
      (A p*((moebius I:ℂ)*(η I*CanonicalRowCompletion.idealRowHom u I)*
      (η p*CanonicalRowCompletion.idealRowHom u p)*
      twistedProfile W σ freq ((I.absNorm:ℝ)/Z^r))) := by ring
    _ = _ := by rw [hn];ring

theorem originalTotal_supported_source (S : Finset (Ideal O)) (P : Ideal O)
    (η : Ideal O →* ℂ) (hη : ∀I,¬CanonicalQuadraticSieve.Supported I → η I=0)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z : ℝ) (u : O) :
    originalTotalPolynomial S P η a W Z r z u=
      originalTotalPolynomial (S.filter CanonicalQuadraticSieve.Supported) P η a W Z r z u := by
  unfold originalTotalPolynomial
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs with hi
  · rfl
  · simp only [heckeIdealCharacter_apply,hη I hi,zero_mul,mul_zero]

def fixedBase (η : Character) (m f : O) : Ideal O →* ℂ :=
  heckeIdealCharacter (idealCoeff η).toMonoidHom (m^6*f^4)

theorem fixedBase_row (η χ : Character) (m f z : O)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n) (I : Ideal O) :
    idealCoeff χ I=fixedBase η m f I*CanonicalRowCompletion.idealRowHom z I := by
  rw [HeckeRowClosure.idealCoeff_eq_row η χ m f z hrow,
    CanonicalRowCompletion.idealRowHom_argument_mul]
  change idealCoeff η I*(CanonicalRowCompletion.idealRowHom (m^6*f^4) I*
    CanonicalRowCompletion.idealRowHom z I)=
    (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*f^4) I)*
    CanonicalRowCompletion.idealRowHom z I
  ring

theorem fixedBase_zero_unsupported (η : Character) (m f : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (I : Ideal O) (hI : ¬CanonicalQuadraticSieve.Supported I) : fixedBase η m f I=0 := by
  by_cases hi : I=0
  · subst I
    change idealCoeff η 0*_=0
    rw [map_zero,zero_mul]
  let n := ConcretePrimeRowBridge.idealGenerator I
  have hn : n≠0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hi
  have hs : Ideal.span {n}=I := ConcretePrimeRowBridge.span_idealGenerator I
  have he := CanonicalRowCompletion.rowTwist_zero_of_not_supported
    (elementHom η) m f 1 n hmLam hm2 (by rwa [hs])
  change elementCoeff η n*CanonicalRowCompletion.idealRowHom (m^6*f^4*1)
    (Ideal.span {n})=0 at he
  rw [mul_one,hs,←idealCoeff_span η hn,hs] at he
  exact he

theorem canonical_inverse_eq_supported_initial (η χ : Character) (m f z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ → ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    polynomial χ true W (Z^r) σ freq=
      originalTotalPolynomial ((idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
        1 (fixedBase η m f) (fun _=>1) (twistedProfile W σ freq) Z r 0 z := by
  rw [inverse_eq_initial_source (fixedBase η m f) χ z (fixedBase_row η χ m f z hrow)
    W Z r σ freq hZ (idealsUpTo ⌈Z^r*b⌉₊)
    (finite_source_cover W (Z^r) b (Real.rpow_pos_of_pos hZ r) hW)]
  exact originalTotal_supported_source _ _ _ (fixedBase_zero_unsupported η m f hmLam hm2)
    _ _ _ _ _ _

theorem inverse_times_conjugate_row_mark_norm (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ → ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z)
    (S P : Finset (Ideal O)) (A : Ideal O → ℂ)
    (hη : ∀p∈P,A p≠0 → η p≠0)
    (hcover : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    ‖polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑p∈P,A p*star (CanonicalRowCompletion.idealRowHom u p))‖=
    ‖∑p∈P,(star (A p)/η p)*originalTotalPolynomial S p η
      (fun _=>1) (twistedProfile W σ freq) Z r z u‖ := by
  have hm : (∑p∈P,(star (A p)/η p)*idealCoeff χ p)=
      star (∑p∈P,A p*star (CanonicalRowCompletion.idealRowHom u p)) := by
    simp only [star_sum,star_mul,star_star]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases ha : A p=0
    · simp [ha]
    · rw [hrow p]
      field_simp [hη p hp ha]
  rw [←inverse_times_mark_eq_initial η χ u hrow W Z r z σ freq hZ S P
    (fun p=>star (A p)/η p) hcover,hm]
  simp only [norm_mul,norm_star]

end SevenEighths.InverseInitialRawDictionary

end

end OAI

end Source2831

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialDetectorSource.lean; sha256: 60842ed81b39c933ede65b0255bfeb6bbe6238dd41a753b3bdc8817aa33ebfa3 -/
section Source2832
namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexConjugate
namespace SevenEighths.InverseInitialDetectorSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open InverseInitialRawDictionary InverseInitialConjugateEnergy
local notation "O" => HeckeFamily.O

def baseCharacter (data : RowData) : Character := data.character ⟨1,one_ne_zero⟩

theorem baseCharacter_coeff (data : RowData) (I : Ideal O) :
    idealCoeff (baseCharacter data) I=fixedBase data.η data.m data.f I := by
  rw [HeckeRowClosure.idealCoeff_eq_row data.η (baseCharacter data) data.m data.f 1
    (data.character_spec ⟨1,one_ne_zero⟩),mul_one]
  rfl

theorem base_nonzero_prime (data : RowData) (P : Ideal O) (hP : Prime P)
    (hN : ((baseCharacter data).modulus.absNorm:ℝ)<(P.absNorm:ℝ)) :
    fixedBase data.η data.m data.f P≠0 := by
  rw [←baseCharacter_coeff]
  exact HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime _ P hP.ne_zero
    (ProbeRaySlots.prime_coprime_of_norm_gt (baseCharacter data) ⟨P,hP⟩ hN)

theorem character_eq_initial (data : RowData) (u : NonzeroElement)
    (W : ℝ→ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    polynomial (data.character u) true W (Z^r) σ freq=
      originalTotalPolynomial
        ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
        1 (fixedBase data.η data.m data.f) (fun _=>1)
        (twistedProfile W σ freq) Z r 0 u.val :=
  canonical_inverse_eq_supported_initial data.η (data.character u) data.m data.f u.val
    data.lambda_dvd data.two_dvd (data.character_spec u) W Z r σ freq b hZ hW

theorem oriented_character_norm_initial (data : RowData) (u : NonzeroElement)
    (χ : Character) (reverse : Bool)
    (hc : ∀I,idealCoeff χ I=if reverse then conj (idealCoeff (data.character u) I)
      else idealCoeff (data.character u) I)
    (W : ℝ→ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    ‖polynomial χ true W (Z^r) σ freq‖=
      ‖originalTotalPolynomial
        ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
        1 (fixedBase data.η data.m data.f) (fun _=>1)
        (twistedProfile (orientedProfile reverse W) σ (orientedFrequency reverse freq))
        Z r 0 u.val‖ := by
  rw [norm_of_oriented_coefficients χ (data.character u) reverse hc true W (Z^r) σ freq
    (Real.rpow_pos_of_pos hZ r)]
  rw [character_eq_initial data u (orientedProfile reverse W) Z r σ
    (orientedFrequency reverse freq) b hZ]
  intro x hx
  apply hW x
  intro hz
  exact hx (by cases reverse <;> simp [orientedProfile,hz])

def primeProfile (V : ℝ→ℂ) (D : ℝ) (ζ : ℂ) (P : Ideal O) : ℂ :=
  V ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(ζ-1)

theorem physical_slot_norm_initial (data : RowData) (u : NonzeroElement)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (W V : ℝ→ℂ) (Z r ell σ freq b bslot a : ℝ) (ζ : ℂ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) (hV : ∀x,V x≠0 → a≤x)
    (hlarge : ((baseCharacter data).modulus.absNorm:ℝ)<a*Z^ell) :
    ‖polynomial (data.character u) true W (Z^r) σ freq*
      HeckePrimeRow.canonicalPrimeAmplitude M H u.val V bslot (Z^ell) ζ‖=
    ‖∑P∈(HeckePrimeAnnular.annulusSet bslot (Z^ell)).filter
        (fun P=>Prime P ∧ P∈RayQuotient.identityClass M H),
      (star (primeProfile V (Z^ell) ζ P)/fixedBase data.η data.m data.f P)*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
          P (fixedBase data.η data.m data.f) (fun _=>1)
          (twistedProfile W σ freq) Z r ell u.val‖ := by
  let Pset := (HeckePrimeAnnular.annulusSet bslot (Z^ell)).filter
    (fun P=>Prime P ∧ P∈RayQuotient.identityClass M H)
  have hc := finite_source_cover W (Z^r) b (Real.rpow_pos_of_pos hZ r) hW
  have hbase (P : Ideal O) (hp : P∈Pset) (ha : primeProfile V (Z^ell) ζ P≠0) :
      fixedBase data.η data.m data.f P≠0 := by
    apply base_nonzero_prime data P (Finset.mem_filter.mp hp).2.1
    have hv : V ((P.absNorm:ℝ)/Z^ell)≠0 := by
      intro hz
      exact ha (by simp [primeProfile,hz])
    exact hlarge.trans_le ((le_div_iff₀ (Real.rpow_pos_of_pos hZ ell)).mp (hV _ hv))
  have he := inverse_times_conjugate_row_mark_norm (fixedBase data.η data.m data.f)
    (data.character u) u.val
    (fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u))
    W Z r ell σ freq hZ (ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊) Pset
    (primeProfile V (Z^ell) ζ) hbase hc
  have hp : HeckePrimeRow.canonicalPrimeAmplitude M H u.val V bslot (Z^ell) ζ=
      ((Z^(-ell/2):ℝ):ℂ)*∑P∈Pset,
        primeProfile V (Z^ell) ζ P*star (CanonicalRowCompletion.idealRowHom u.val P) := by
    unfold HeckePrimeRow.canonicalPrimeAmplitude
    rw [normalization_eq Z ell hZ]
    congr 1
    apply Finset.sum_congr rfl
    intro P hP
    change star (CanonicalRowCompletion.idealRowHom u.val P)*V _*_ =
      (V _*_)*star (CanonicalRowCompletion.idealRowHom u.val P)
    ring
  rw [hp,←mul_assoc,he]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  rw [originalTotal_supported_source _ _ _
    (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd)]

end SevenEighths.InverseInitialDetectorSource

end

end OAI

end Source2832

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawRadial.lean; sha256: 10e9ccaaa23bb1ddae66bc3e0bdba5873bbd76f081a0003742ae8ceba36e0065 -/
section Source2833
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawRadial
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialConjugateEnergy CanonicalQuadraticSieve
open ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O

theorem exists_raw_radial_majorant :
    ∃Φ : 𝓢(ℝ,ℂ),HasCompactSupport (Φ:ℝ→ℂ) ∧
      (∀x,0≤(Φ x).re) ∧ (∀x∈Set.Icc (0:ℝ) 1,Φ x=1) := by
  have hsub : Set.Icc (0:ℝ) 1⊆Set.Ioo (-1) 2 := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v : ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv : ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf : ContDiff ℝ ∞ f).pow 2)
  have hsupp : Function.support v⊆Set.Icc (-1) 2 := by
    intro x hx
    have hn : x∈Function.support f := by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  have hvc:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

private theorem admissible_one : Admissible (1:Ideal O) := by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

theorem finite_raw_le_initial_smoothed (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀x,0≤(Φ x).re) (hone : ∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data : RowData) (W : ℝ→ℂ) (b Z r σ t H : ℝ)
    (hZ : 0<Z) (hH : 0<H) (hW : ∀x,W x≠0 → x≤b)
    (rows : Finset NonzeroElement)
    (hrows : ∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H) :
    (∑u∈rows,‖polynomial (data.character u) true W (Z^r) σ t‖^2)≤
      smoothedEnergy Φ H
        (originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter Supported)
          1 (fixedBase data.η data.m data.f) (fun _=>1)
          (twistedProfile W σ t) Z r 0) := by
  let S:=(ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter Supported
  let f:=originalTotalPolynomial S 1 (fixedBase data.η data.m data.f) (fun _=>1)
    (twistedProfile W σ t) Z r 0
  have hsum : Summable (fun u:O=>radialWeight Φ H u*‖f u‖^2) :=
    (original_smoothed_overlap_triangle S admissible_one
      (fun n hn _=>(Finset.mem_filter.mp hn).2) (fixedBase data.η data.m data.f)
      (fun _=>1) (twistedProfile W σ t) hZ r 0 (fun _=>0) Φ (fun x _=>hΦ x) hH).1
  have he (u : NonzeroElement) (hu : u∈rows) :
      ‖polynomial (data.character u) true W (Z^r) σ t‖^2=
        radialWeight Φ H u.val*‖f u.val‖^2 := by
    have hn : ‖eisEmbedding u.val‖^2/H∈Set.Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) hH.le,?_⟩
      apply (div_le_one hH).mpr
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    rw [character_eq_initial data u W Z r σ t b hZ hW]
    change ‖f u.val‖^2=(Φ (‖eisEmbedding u.val‖^2/H)).re*‖f u.val‖^2
    rw [hone _ hn,Complex.one_re,one_mul]
  calc
    _=∑u∈rows,radialWeight Φ H u.val*‖f u.val‖^2:=Finset.sum_congr rfl he
    _=∑u∈rows.image Subtype.val,radialWeight Φ H u*‖f u‖^2:=by
      rw [Finset.sum_image (fun a _ b _ hab=>Subtype.val_injective hab)]
    _≤∑'u:O,radialWeight Φ H u*‖f u‖^2:=hsum.sum_le_tsum _
      (fun u _=>mul_nonneg (hΦ _) (sq_nonneg _))
    _= _:=rfl

end SevenEighths.DetectorDictionaryInverseRawRadial

end

end OAI

end Source2833

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialExcludedSource.lean; sha256: 1262e9bb255a2aa43e72385673bc74dce0c4c6d9dd363684428c355c8f4ff79b -/
section Source2834
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedSource
open InverseInitialOverlap
local notation "O"=>ActualEisensteinCubic.O

def columns (S:Finset (Ideal O))(P j:Ideal O):Finset (Ideal O):=
  (original S P j).image (idealQuotient j)

theorem quotient_properties {P j n:Ideal O}(hn:Squarefree n)(hg:gcd n P=j):
    Squarefree (idealQuotient j n) ∧ IsCoprime (idealQuotient j n) P ∧
      j*idealQuotient j n=n := by
  have hjn:j∣n:=hg ▸ GCDMonoid.gcd_dvd_left n P
  exact ⟨hn.squarefree_of_dvd (idealQuotient_dvd hjn),by
    rw [←hg];exact squarefree_quotient_gcd_coprime n P hn,idealQuotient_mul hjn⟩

theorem reconstruct_properties {P j c:Ideal O}(hP:Squarefree P)(hj:j∣P)
    (hc:Squarefree c)(hcp:IsCoprime c P):
    Squarefree (j*c) ∧ gcd (j*c) P=j := by
  exact ⟨squarefree_mul_iff.mpr ⟨(hcp.mono (dvd_refl _) hj).symm.isRelPrime,
    hP.squarefree_of_dvd hj,hc⟩,gcd_mul_of_coprime_divisor j c P hj hcp⟩

theorem mem_columns {S:Finset (Ideal O)}{P j c:Ideal O}
    (hP:Squarefree P)(hj:j∣P):
    c∈columns S P j ↔ Squarefree c ∧ IsCoprime c P ∧ j*c∈S := by
  constructor
  · intro hc
    obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hc
    obtain ⟨hnS,hns,hng⟩:=mem_original.mp hn
    obtain ⟨hcs,hcp,he⟩:=quotient_properties hns hng
    exact ⟨hcs,hcp,he.symm ▸ hnS⟩
  · rintro ⟨hcs,hcp,hnS⟩
    obtain ⟨hns,hng⟩:=reconstruct_properties hP hj hcs hcp
    refine Finset.mem_image.mpr ⟨j*c,mem_original.mpr ⟨hnS,hns,hng⟩,?_⟩
    exact quotient_mul_cancel (ne_zero_of_dvd_ne_zero hP.ne_zero hj)

theorem sum_reconstruct (S:Finset (Ideal O)){P j:Ideal O}
    (_hP:Squarefree P)(_hj:j∣P)(f:Ideal O→ℂ):
    (∑n∈original S P j,f n)=∑c∈columns S P j,f (j*c) := by
  rw [columns,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [(quotient_properties (mem_original.mp hn).2.1 (mem_original.mp hn).2.2).2.2]
  · intro n hn n' hn' he
    have h1:=(quotient_properties (mem_original.mp hn).2.1 (mem_original.mp hn).2.2).2.2
    have h2:=(quotient_properties (mem_original.mp hn').2.1 (mem_original.mp hn').2.2).2.2
    rw [←h1,←h2,he]

theorem cutoff_argument (j c:Ideal O)(X:ℝ):
    ((j*c).absNorm:ℝ)/X=(c.absNorm:ℝ)/(X/(j.absNorm:ℝ)) := by
  rw [map_mul,Nat.cast_mul,div_div_eq_mul_div]
  ring

theorem coefficient_identity (ψ:Ideal O→*ℂ){P j c:Ideal O}
    (hj:j∣P)(hcp:IsCoprime c P):
    (moebius (j*c):ℂ)*ψ (j*c)=(moebius j:ℂ)*ψ j*((moebius c:ℂ)*ψ c) := by
  rw [((hcp.mono (dvd_refl _) hj).symm.isRelPrime).moebius_mul,Int.cast_mul,map_mul]
  ring

theorem polynomial_slice (S:Finset (Ideal O)){P j:Ideal O}
    (hP:Squarefree P)(hj:j∣P)(ψ:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(X:ℝ):
    (∑n∈original S P j,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
    ((moebius j:ℂ)*ψ j)*∑c∈columns S P j,(moebius c:ℂ)*ψ c*a (j*c)*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  rw [sum_reconstruct S hP hj,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [coefficient_identity ψ hj ((mem_columns hP hj).mp hc).2.1,cutoff_argument]
  ring

theorem polynomial_decomposition (S:Finset (Ideal O)){P:Ideal O}(hP:Squarefree P)
    (ψ:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(X:ℝ):
    (∑n∈S,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
    ∑j∈idealDivisors P,((moebius j:ℂ)*ψ j)*
      ∑c∈columns S P j,(moebius c:ℂ)*ψ c*a (j*c)*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have hs:(∑n∈S,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
      ∑n∈S.filter Squarefree,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hs:Squarefree n
    · rw [ite_eq_left hs]
    · simp only [ite_eq_right hs,moebius_of_not_squarefree hs,Int.cast_zero,zero_mul]
  rw [hs,sum_original_partition S hP]
  apply Finset.sum_congr rfl
  intro j hj
  exact polynomial_slice S hP ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W X

end SevenEighths.InverseInitialExcludedSource

end

end OAI

end Source2834

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialExcludedPolynomial.lean; sha256: 4ed3b93565bf3df5ed5a33ab05398968ba57ef9d0743c729cd1d9b3322c77f5e -/
section Source2835
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialExcludedPolynomial
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge
open InverseInitialExcludedSource IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

theorem prime_product_squarefree (S:Finset (Ideal O))(hS:∀P∈S,Prime P):
    Squarefree (∏P∈S,P) := by
  have hz:(∏P∈S,P)≠0:=Finset.prod_ne_zero_iff.mpr (fun P hP=>(hS P hP).ne_zero)
  apply (squarefree_iff_nodup_normalizedFactors hz).mpr
  have he:normalizedFactors (∏P∈S,P)=S.val:=by
    simpa using normalizedFactors_prod_of_prime (m:=S.val) (fun P hP=>hS P hP)
  rw [he]
  exact S.nodup

theorem deleted_coefficient_product (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(I:Ideal O):
    idealCoeff (χ.excludePrimes S hS) I=
      if IsCoprime I (∏P∈S,P) then idealCoeff χ I else 0 := by
  rw [idealCoeff_excludePrimes,IsCoprime.prod_right_iff]
  congr 1

theorem residual_source (χ:Character)(S A:Finset (Ideal O))(hS:∀P∈S,Prime P)
    {j:Ideal O}(hj:j∣∏P∈S,P)(W:ℝ→ℂ)(X:ℝ)
    (hcover:∀I:Ideal O,I≠0→W ((I.absNorm:ℝ)/X)≠0→I∈A):
    (∑c∈columns A (∏P∈S,P) j,(moebius c:ℂ)*idealCoeff χ c*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))))=
    ∑'c:Ideal O,(moebius c:ℂ)*idealCoeff (χ.excludePrimes S hS) c*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have hP:=prime_product_squarefree S hS
  have hj0:=ne_zero_of_dvd_ne_zero hP.ne_zero hj
  symm
  calc
    _ = ∑c∈columns A (∏P∈S,P) j,(moebius c:ℂ)*idealCoeff (χ.excludePrimes S hS) c*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
      apply tsum_eq_sum
      intro c hc
      by_cases hcs:Squarefree c
      · by_cases hcp:IsCoprime c (∏P∈S,P)
        · have hw:W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ)))=0:=by
            by_contra hw
            apply hc
            apply (mem_columns hP hj).mpr
            refine ⟨hcs,hcp,hcover (j*c) (mul_ne_zero hj0 hcs.ne_zero) ?_⟩
            rwa [cutoff_argument]
          rw [hw,mul_zero]
        · rw [deleted_coefficient_product,ite_eq_right hcp,mul_zero,zero_mul]
      · rw [moebius_of_not_squarefree hcs,Int.cast_zero,zero_mul,zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [deleted_coefficient_product,ite_eq_left ((mem_columns hP hj).mp hc).2.1]

theorem source_decomposition (χ:Character)(S A:Finset (Ideal O))(hS:∀P∈S,Prime P)
    (W:ℝ→ℂ)(X:ℝ)(hcover:∀I:Ideal O,I≠0→W ((I.absNorm:ℝ)/X)≠0→I∈A):
    (∑I∈A,(moebius I:ℂ)*idealCoeff χ I*W ((I.absNorm:ℝ)/X))=
    ∑j∈idealDivisors (∏P∈S,P),((moebius j:ℂ)*idealCoeff χ j)*
      ∑'c:Ideal O,(moebius c:ℂ)*idealCoeff (χ.excludePrimes S hS) c*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have he:=polynomial_decomposition A (prime_product_squarefree S hS)
    (idealCoeff χ).toMonoidHom (fun _=>1) W X
  simp only [mul_one] at he
  trans ∑j∈idealDivisors (∏P∈S,P),((moebius j:ℂ)*idealCoeff χ j)*
    ∑c∈columns A (∏P∈S,P) j,(moebius c:ℂ)*idealCoeff χ c*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ)))
  · exact he
  apply Finset.sum_congr rfl
  intro j hj
  rw [residual_source χ S A hS ((mem_idealDivisors (prime_product_squarefree S hS).ne_zero).mp hj) W X hcover]

theorem polynomial_all_ideals (χ:Character)(W:ℝ→ℂ)(X σ t:ℝ):
    polynomial χ true W X σ t=(X:ℂ)^(-(1/2:ℂ))*
      ∑'I:Ideal O,(moebius I:ℂ)*idealCoeff χ I*
        (W ((I.absNorm:ℝ)/X)*(((I.absNorm:ℝ)/X:ℝ):ℂ)^(-shift σ t)) := by
  unfold polynomial
  congr 1
  let f:Ideal O→ℂ:=fun I=>(moebius I:ℂ)*idealCoeff χ I*
    (W ((I.absNorm:ℝ)/X)*(((I.absNorm:ℝ)/X:ℝ):ℂ)^(-shift σ t))
  have hf:Function.support f⊆{I:Ideal O|I≠0}:=by
    intro I hi hz
    subst I
    exact hi (by simp only [f,map_zero,mul_zero,zero_mul])
  have he:=tsum_subtype_eq_of_support_subset hf
  calc
    _=∑'I:{I:Ideal O//I≠0},f I.val:=by
      apply tsum_congr
      intro I
      simp only [summand,coefficient,ite_true,HeckeDyadic.norm,f]
      ring
    _=_:=he

theorem scale_normalization (X n:ℝ)(hX:0<X)(hn:0<n):
    (n:ℂ)^(-(1/2:ℂ))*((X/n:ℝ):ℂ)^(-(1/2:ℂ))=(X:ℂ)^(-(1/2:ℂ)) := by
  rw [←Complex.mul_cpow_ofReal_nonneg hn.le (div_pos hX hn).le,
    ←Complex.ofReal_mul,mul_div_cancel₀ _ hn.ne']

theorem inverse_polynomial_decomposition (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(W:ℝ→ℂ)(X σ t b:ℝ)(hX:0<X)
    (hW:∀x,W x≠0→x≤b):
    polynomial χ true W X σ t=
    ∑j∈idealDivisors (∏P∈S,P),
      ((moebius j:ℂ)*idealCoeff χ j*(j.absNorm:ℂ)^(-(1/2:ℂ)))*
        polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t := by
  let A:=ConcretePrimeRowBridge.idealsUpTo ⌈X*b⌉₊
  let V:ℝ→ℂ:=fun x=>W x*(x:ℂ)^(-shift σ t)
  have hc:∀I:Ideal O,I≠0→W ((I.absNorm:ℝ)/X)≠0→I∈A:=
    InverseInitialRawDictionary.finite_source_cover W X b hX hW
  have hcv:∀I:Ideal O,I≠0→V ((I.absNorm:ℝ)/X)≠0→I∈A:=by
    intro I hi hv
    apply hc I hi
    intro hw
    exact hv (by simp [V,hw])
  rw [polynomial_eq_finite χ true W X σ t A hc]
  have hsource:=source_decomposition χ S A hS V X hcv
  have hfinite:(∑I∈A,coefficient χ true I*W ((I.absNorm:ℝ)/X)*
      (((I.absNorm:ℝ)/X:ℝ):ℂ)^(-shift σ t))=
      ∑I∈A,(moebius I:ℂ)*idealCoeff χ I*V ((I.absNorm:ℝ)/X):=by
    apply Finset.sum_congr rfl
    intro I hi
    simp only [coefficient,ite_true,V]
    ring
  rw [hfinite,hsource,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd: j∣∏P∈S,P:=(mem_idealDivisors (prime_product_squarefree S hS).ne_zero).mp hj
  have hj0:j≠0:=ne_zero_of_dvd_ne_zero (prime_product_squarefree S hS).ne_zero hjd
  have hjpos:0<(j.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  rw [polynomial_all_ideals]
  have hn:=scale_normalization X (j.absNorm:ℝ) hX hjpos
  simp only [Complex.ofReal_natCast] at hn
  dsimp only [V]
  rw [←hn]
  ring

end SevenEighths.InverseInitialExcludedPolynomial

end

end OAI

end Source2835

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialExcludedGeometry.lean; sha256: 9d118674c8a153c99ca10a67930a93b771b8558aa51840d815114de68e4ede38 -/
section Source2836
namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace SevenEighths.InverseInitialExcludedGeometry
open HeckeFamily InverseInitialExcludedPolynomial IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O

def adjustedLength (Z r:ℝ)(j:Ideal O):ℝ:=r-Real.log (j.absNorm:ℝ)/Real.log Z

theorem adjusted_scale (Z r:ℝ)(hZ:1<Z){j:Ideal O}(hj:j≠0):
    Z^adjustedLength Z r j=Z^r/(j.absNorm:ℝ) := by
  have hjpos:0<(j.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj)
  have hzpos:=lt_trans zero_lt_one hZ
  rw [adjustedLength,Real.rpow_sub hzpos]
  congr 1
  rw [Real.rpow_def_of_pos hzpos]
  have hl:Real.log Z≠0:=(Real.log_pos hZ).ne'
  rw [mul_div_cancel₀ _ hl,Real.exp_log hjpos]

theorem divisor_norm_bounds {P j:Ideal O}(hP:P≠0)(hj:j∣P):
    1≤(j.absNorm:ℝ) ∧ (j.absNorm:ℝ)≤(P.absNorm:ℝ) := by
  have hj0:=ne_zero_of_dvd_ne_zero hP hj
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  · exact_mod_cast Nat.le_of_dvd
      (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP))
      (map_dvd Ideal.absNorm hj)

theorem adjustedLength_bounds (Z r η:ℝ)(hZ:1<Z){P j:Ideal O}
    (hP:P≠0)(hj:j∣P)(hlarge:Real.log (P.absNorm:ℝ)≤η*Real.log Z):
    r-η≤adjustedLength Z r j ∧ adjustedLength Z r j≤r := by
  obtain ⟨hn,hnP⟩:=divisor_norm_bounds hP hj
  have hl:0≤Real.log (j.absNorm:ℝ):=Real.log_nonneg hn
  have hu:Real.log (j.absNorm:ℝ)≤η*Real.log Z:=
    (Real.log_le_log (lt_of_lt_of_le zero_lt_one hn) hnP).trans hlarge
  have hd:Real.log (j.absNorm:ℝ)/Real.log Z≤η:=(div_le_iff₀ (Real.log_pos hZ)).mpr hu
  have hd0:0≤Real.log (j.absNorm:ℝ)/Real.log Z:=div_nonneg hl (Real.log_pos hZ).le
  dsimp [adjustedLength]
  constructor <;> linarith

theorem adjustedLength_eventually (P:Ideal O)(hP:P≠0)(η:ℝ)(hη:0<η):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀r:ℝ,∀j∈idealDivisors P,
      r-η≤adjustedLength Z r j ∧ adjustedLength Z r j≤r := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (P.absNorm:ℝ)/η))] with Z hZ hlog
  refine ⟨hZ,fun r j hj=>adjustedLength_bounds Z r η hZ hP ((mem_idealDivisors hP).mp hj) ?_⟩
  exact (div_le_iff₀ hη).mp hlog |>.trans_eq (mul_comm _ _)

theorem prime_coprime_of_norm_gt {P I:Ideal O}(hP:Prime P)(hI:I≠0)
    (hN:(I.absNorm:ℝ)<(P.absNorm:ℝ)):IsCoprime P I := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hIJ hJ
  have hmax:=(Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have heq:=hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hIJ
  have hd:P∣I:=Ideal.dvd_iff_le.mpr hIJ
  exact (not_le_of_gt hN) (divisor_norm_bounds hI hd).2

theorem live_prime_deleted_coefficient (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(V:ℝ→ℂ)(a Y:ℝ)(hY:0<Y)
    (hV:∀x,V x≠0→a≤x)(hlarge:((∏Q∈S,Q).absNorm:ℝ)<a*Y)
    (P:Ideal O)(hP:Prime P)(hvp:V ((P.absNorm:ℝ)/Y)≠0):
    idealCoeff (χ.excludePrimes S hS) P=idealCoeff χ P := by
  rw [deleted_coefficient_product,ite_eq_left]
  apply prime_coprime_of_norm_gt hP (prime_product_squarefree S hS).ne_zero
  exact hlarge.trans_le ((le_div_iff₀ hY).mp (hV _ hvp))

theorem prime_slot_unchanged (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(V:ℝ→ℂ)(a Y:ℝ)(hY:0<Y)
    (hV:∀x,V x≠0→a≤x)(hlarge:((∏Q∈S,Q).absNorm:ℝ)<a*Y)
    (P:Ideal O)(hP:Prime P):
    idealCoeff (χ.excludePrimes S hS) P*V ((P.absNorm:ℝ)/Y)=
      idealCoeff χ P*V ((P.absNorm:ℝ)/Y) := by
  by_cases hv:V ((P.absNorm:ℝ)/Y)=0
  · rw [hv,mul_zero,mul_zero]
  · rw [live_prime_deleted_coefficient χ S hS V a Y hY hV hlarge P hP hv]

end SevenEighths.InverseInitialExcludedGeometry

end

end OAI

end Source2836

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialExcludedPeriod.lean; sha256: 6117215462c6dc54bea95092141366fe24ffe9fcd717bd33ed6e6721f6e86785 -/
section Source2837
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialExcludedPeriod
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CanonicalCoefficientClass ConcretePrimeRowBridge IdealMobiusDivisorSum
open UniqueFactorizationMonoid HeckeFamily
local notation "O" => ActualEisensteinCubic.O

def deletedPeriod (q:ℕ):ℕ := 2592*q^2

theorem deletedPeriod_ne_zero (q:ℕ)(hq:q≠0):deletedPeriod q≠0 := by
  unfold deletedPeriod
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hq)

theorem fixed_bad_divides_reflection (q:ℕ)(P:Ideal O)(hP:P∈fixedBadPrimes):
    P∣Ideal.span {reflectionConductor q} := by
  change P∈({Ideal.span {goodLambda},Ideal.span {(2:O)}}:Finset (Ideal O)) at hP
  rcases Finset.mem_insert.mp hP with rfl|hP
  · apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_singleton_le_span_singleton.mpr
    have h3:goodLambda∣(3:O):=CubicEisenstein.halfPrimary_lambda_dvd_three
    apply h3.trans
    refine ⟨(864*q:ℕ),?_⟩
    unfold reflectionConductor
    push_cast
    ring
  · rw [Finset.mem_singleton.mp hP]
    apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_singleton_le_span_singleton.mpr
    refine ⟨(1296*q:ℕ),?_⟩
    unfold reflectionConductor
    push_cast
    ring

theorem excluded_mem_iff (q:ℕ)(hq:q≠0)(P:Ideal O):
    P∈reflectionExcludedPrimes q ↔ Prime P ∧ P∣Ideal.span {reflectionConductor q} := by
  constructor
  · intro hP
    refine ⟨reflectionExcludedPrimes_prime q P hP,?_⟩
    rcases Finset.mem_union.mp hP with hb|hp
    · exact fixed_bad_divides_reflection q P hb
    · exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp)
  · rintro ⟨hp,hd⟩
    exact reflectionConductor_prime_mem q hq P hp hd

theorem excluded_product_divides_reflection (q:ℕ)(hq:q≠0):
    (∏P∈reflectionExcludedPrimes q,P)∣Ideal.span {reflectionConductor q} := by
  apply support_product_dvd (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))
  intro P hP
  apply Multiset.mem_toFinset.mpr
  apply (Ideal.mem_normalizedFactors_iff
    (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))).mpr
  obtain ⟨hp,hd⟩:= (excluded_mem_iff q hq P).mp hP
  exact ⟨Ideal.isPrime_of_prime hp,Ideal.dvd_iff_le.mp hd⟩

theorem deleted_reflection_ideal (q:ℕ):
    Ideal.span {reflectionConductor (deletedPeriod q)}=
      (Ideal.span {reflectionConductor q}:Ideal O)^2 := by
  rw [Ideal.span_singleton_pow]
  congr 1
  unfold reflectionConductor deletedPeriod
  push_cast
  ring_nf

theorem deleted_excluded_eq (q:ℕ)(hq:q≠0):
    reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q := by
  ext P
  rw [excluded_mem_iff _ (deletedPeriod_ne_zero q hq),excluded_mem_iff q hq,
    deleted_reflection_ideal]
  constructor
  · rintro ⟨hp,hd⟩
    exact ⟨hp,hp.dvd_of_dvd_pow hd⟩
  · rintro ⟨hp,hd⟩
    exact ⟨hp,hd.trans (dvd_pow_self _ (by decide:2≠0))⟩

theorem deleted_period_ideal (q:ℕ):
    (Ideal.span {(deletedPeriod q:O)}:Ideal O)=
      Ideal.span {(q:O)}*Ideal.span {reflectionConductor q} := by
  rw [Ideal.span_singleton_mul_span_singleton]
  congr 1
  unfold deletedPeriod reflectionConductor
  push_cast
  ring_nf

theorem deleted_period_le_modulus (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    Ideal.span {(deletedPeriod q:O)}≤
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus := by
  change Ideal.span {(deletedPeriod q:O)}≤χ.modulus*(∏P∈reflectionExcludedPrimes q,P)
  rw [deleted_period_ideal]
  exact Ideal.mul_mono hperiod (Ideal.dvd_iff_le.mp (excluded_product_divides_reflection q hq))

theorem deleted_element_period (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))) := by
  intro x y hxy
  apply HeckeRowClosure.elementHom_periodic
  exact deleted_period_le_modulus χ q hq hperiod (Ideal.mul_le_left hxy)

theorem deleted_base_gates (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    (∀x,‖HeckeRowClosure.elementHom
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))) := by
  exact ⟨deletedPeriod_ne_zero q hq,deleted_excluded_eq q hq,
    HeckeRowClosure.elementHom_norm _,deleted_element_period χ q hq hperiod⟩

end SevenEighths.InverseInitialExcludedPeriod

end

end OAI

end Source2837

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialExcludedElement.lean; sha256: f0cc33bb400ff2739b90b0511a7e6f522e63dd8d415591e33b5ca3bfe578cb04 -/
section Source2838
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialExcludedPeriod
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CanonicalCoefficientClass HeckeFamily InverseInitialRayAttachment
local notation "O"=>ActualEisensteinCubic.O

theorem elementCharacter_eq_elementHom (χ:Character)(hproper:χ.modulus≠⊤):
    elementCharacter (idealCoeff χ).toMonoidHom=HeckeRowClosure.elementHom χ := by
  let:Nontrivial (O⧸χ.modulus):=Ideal.Quotient.nontrivial_iff.mpr hproper
  ext z
  change idealCoeff χ (Ideal.span {z})=elementCoeff χ z
  by_cases hz:z=0
  · subst z
    simp only [Ideal.span_singleton_zero,←Ideal.zero_eq_bot,
      elementCoeff,map_zero,MulChar.map_zero]
  · exact idealCoeff_span χ hz

theorem deleted_modulus_proper (χ:Character)(q:ℕ):
    (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus≠⊤ := by
  have htwo:(Ideal.span {(2:O)}:Ideal O)∈reflectionExcludedPrimes q:=
    reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes])
  have hle:(χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus≤
      Ideal.span {(2:O)}:=by
    change χ.modulus*(∏P∈reflectionExcludedPrimes q,P)≤Ideal.span {(2:O)}
    exact Ideal.mul_le_right.trans (Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem (fun P=>P) htwo))
  intro he
  exact twoIdeal_maximal.ne_top (top_le_iff.mp (he ▸ hle))

theorem deleted_physical_element_eq (χ:Character)(q:ℕ):
    elementCharacter (idealCoeff
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom=
      HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)) :=
  elementCharacter_eq_elementHom _ (deleted_modulus_proper χ q)

theorem deleted_physical_base_gates (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    (∀x,‖elementCharacter (idealCoeff
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (elementCharacter (idealCoeff
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom) := by
  rw [deleted_physical_element_eq]
  exact deleted_base_gates χ q hq hperiod

end SevenEighths.InverseInitialExcludedPeriod

end

end OAI

end Source2838

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerSelector.lean; sha256: 78454dbd8e2c250d1a33c88c6231bd812c0edec721ac6480ce77869457de5e6e -/
section Source2839
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseMoment
namespace SevenEighths.InverseInitialEnergyCallerSelector
local notation "Eis" => ActualEisensteinCubic.O

theorem mask_nonzero_coprime (F : Finset (Ideal Eis)) (j : Ideal Eis) (hj : Admissible j)
    (A : Finset (primePool F))
    (hm : rowCoprimeMask (fun i : primePool F=>i.val) A (primaryGenerator j)≠0) :
    IsCoprime (∏ i∈A,i.val) j := by
  have hspan := (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1
  apply IsCoprime.prod_left
  intro i hi
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra htop
  have he := Ideal.IsMaximal.eq_of_le (inferInstance : i.val.IsMaximal) htop
    (show (i.val : Ideal Eis) ≤ (i.val : Ideal Eis) ⊔ j from le_sup_left)
  have hmem : primaryGenerator j∈i.val := by
    rw [he]
    apply (show j ≤ (i.val : Ideal Eis) ⊔ j from le_sup_right)
    have hjmem : primaryGenerator j ∈ Ideal.span {primaryGenerator j} :=
      Ideal.subset_span (Set.mem_singleton _)
    rw [hspan] at hjmem
    exact hjmem
  apply hm
  unfold rowCoprimeMask
  exact ite_eq_left ⟨i,hi,hmem⟩

theorem reconstructedSelector_profile
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (a : Ideal Eis→ℂ) (W : Ideal Eis→ℂ)
    (A : Finset (primePool (columns S P j)))
    (hA : Squarefree (∏ i∈A,i.val))
    (hcover : residual P j∣(∏ i∈A,i.val) → W (∏ i∈A,i.val)≠0 →
      IsCoprime (∏ i∈A,i.val) j → reconstruct P j (∏ i∈A,i.val)∈S) :
    reconstructedSelector S P j a A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) =
    a (reconstruct P j (∏ i∈A,i.val)) * (if residual P j∣(∏ i∈A,i.val) then 1 else 0) *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) := by
  by_cases hm : rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j)=0
  · simp only [hm,mul_zero,zero_mul]
  by_cases hW : W (∏ i∈A,i.val)=0
  · simp only [hW,mul_zero]
  have hcop := mask_nonzero_coprime (columns S P j) j (admissible_of_dvd hP hj) A hm
  by_cases hd : residual P j∣(∏ i∈A,i.val)
  · have hmem := (mem_columns hP.2.1 hj).mpr ⟨hA,hcop,hd,hcover hd hW hcop⟩
    simp only [reconstructedSelector,hmem,ite_true,hd,mul_one]
  · have hn : (∏ i∈A,i.val)∉columns S P j := by
      intro h
      exact hd ((mem_columns hP.2.1 hj).mp h).2.2.1
    simp only [reconstructedSelector,hn,ite_false,hd,mul_zero,zero_mul]

theorem singleton_primeMark {ι : Type*} [DecidableEq ι] (B A : Finset ι) :
    primeMark B (fun i=>{i}) (fun _ _=>(1:ℂ)) A = if B⊆A then 1 else 0 := by
  classical
  simp only [primeMark,primeSlot,Finset.sum_singleton]
  by_cases h : B⊆A
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i hi
    exact ite_eq_left (h hi)
  · rw [ite_eq_right h]
    obtain ⟨i,hi,hn⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (ite_eq_right hn)

theorem forcing_primeMark {ι : Type*} [DecidableEq ι]
    (Q : ι→Ideal Eis) [∀ i,(Q i).IsMaximal] (hinj : Function.Injective Q)
    (B A : Finset ι) :
    primeMark B (fun i=>{i}) (fun _ _=>(1:ℂ)) A =
      if (∏ i∈B,Q i)∣(∏ i∈A,Q i) then 1 else 0 := by
  classical
  have hd : (∏ i∈B,Q i)∣(∏ i∈A,Q i) ↔ B⊆A := by
    constructor
    · intro h i hi
      exact (FirstCauchyArithmetic.family_prime_dvd_product_iff Q hinj A i).mp
        ((Finset.dvd_prod_of_mem Q hi).trans h)
    · intro h
      exact Finset.prod_dvd_prod_of_subset B A Q h
  rw [singleton_primeMark,hd]
  split_ifs <;> rfl

theorem reconstructedSelector_forced_mark
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (a : Ideal Eis→ℂ) (W : Ideal Eis→ℂ)
    (B A : Finset (primePool (columns S P j)))
    (hB : (∏ i∈B,i.val)=residual P j)
    (hA : Squarefree (∏ i∈A,i.val))
    (hcover : residual P j∣(∏ i∈A,i.val) → W (∏ i∈A,i.val)≠0 →
      IsCoprime (∏ i∈A,i.val) j → reconstruct P j (∏ i∈A,i.val)∈S) :
    reconstructedSelector S P j a A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) =
    a (reconstruct P j (∏ i∈A,i.val)) * primeMark B (fun i=>{i}) (fun _ _=>(1:ℂ)) A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) := by
  rw [forcing_primeMark (fun i : primePool (columns S P j)=>i.val) Subtype.val_injective B A,hB]
  exact reconstructedSelector_profile S hP hj a W A hA hcover

end SevenEighths.InverseInitialEnergyCallerSelector

end

end OAI

end Source2839
