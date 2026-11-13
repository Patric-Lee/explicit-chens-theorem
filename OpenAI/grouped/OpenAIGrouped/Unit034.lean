import OpenAIGrouped.Unit033
import OpenAIGrouped.Unit012
import OpenAIGrouped.Unit026
import OpenAIGrouped.Unit031
import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import OpenAIGrouped.Unit007

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianFlow.lean; sha256: 86398c70748f960142fac626a425eed4d91623fd4b8a894746c1916126ebf975 -/
section Source1360
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Filter Set Metric
namespace SevenEighths.ProbePhysical

def gaussianFlow (R : ℝ) (z : ℂ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
    Complex.exp (-((Real.log R:ℂ)+z)^2/4)
lemma gaussianFlow_analytic (R : ℝ) (z : ℂ) : AnalyticAt ℂ (gaussianFlow R) z := by
  unfold gaussianFlow
  fun_prop
lemma gaussianFlow_real (R : ℝ) (hR : 0<R) (s : ℝ) :
    gaussianFlow R (s:ℂ)=gaussianMellinProfile (R*Real.exp s) := by
  unfold gaussianFlow gaussianMellinProfile
  rw [←Complex.ofReal_log (mul_pos hR (Real.exp_pos _)).le,Real.log_mul hR.ne' (Real.exp_pos _).ne',Real.log_exp,
    Complex.ofReal_add]

lemma iteratedDeriv_restrict_real (f : ℂ→ℂ)
    (hf : ∀x : ℝ,AnalyticAt ℂ f (x:ℂ)) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ=>f (y:ℂ)) x=iteratedDeriv n f (x:ℂ) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ',iteratedDeriv_succ']
    have he : deriv (fun y : ℝ=>f (y:ℂ))=(fun y : ℝ=>deriv f (y:ℂ)) := by
      funext y
      exact (hf y).differentiableAt.hasDerivAt.comp_ofReal.deriv
    rw [he]
    exact ih (deriv f) (fun y=>(hf y).deriv)

lemma gaussianFlow_disk_bound (a L : ℝ) (_hL : 0≤L) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ∀z∈Metric.closedBall (y:ℂ) 1,‖gaussianFlow R z‖≤C*R^(-a) := by
  let c := ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖
  let B := Real.exp (a^2+1/4+|a| *(L+1))
  have hc : 0≤c := norm_nonneg _
  have hB : 0<B := Real.exp_pos _
  refine ⟨(c+1)*B,by positivity,?_⟩
  intro R hR y hy z hz
  have hd : ‖z-(y:ℂ)‖≤1 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hzr := (Complex.abs_re_le_norm (z-(y:ℂ))).trans hd
  have hzi := (Complex.abs_im_le_norm (z-(y:ℂ))).trans hd
  simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at hzr hzi
  have hre : |z.re|≤L+1 := by
    have h := abs_add_le (z.re-y) y
    have he : z.re-y+y=z.re := by ring
    rw [he] at h
    linarith
  have hsq : z.im^2≤1 := by nlinarith [(abs_le.mp hzi).1,(abs_le.mp hzi).2]
  have hmul : -(a*z.re)≤|a| *(L+1) := by
    calc
      _ ≤ |a*z.re| := neg_le_abs _
      _ = |a| *|z.re| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hre (abs_nonneg _)
  have he : (-((Real.log R:ℂ)+z)^2/4).re=(z.im^2-(Real.log R+z.re)^2)/4 := by
    simp [pow_two,Complex.mul_re]
  unfold gaussianFlow
  rw [norm_mul,Complex.norm_exp,he]
  have hb : Real.exp ((z.im^2-(Real.log R+z.re)^2)/4)≤B*R^(-a) := by
    rw [Real.rpow_def_of_pos hR,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ((Real.log R+z.re)/2-a)]
  calc
    _ ≤ c*(B*R^(-a)) := mul_le_mul_of_nonneg_left hb hc
    _ ≤ (c+1)*B*R^(-a) := by nlinarith [mul_pos hB (Real.rpow_pos_of_pos hR (-a))]

lemma gaussianFlow_derivative_bound (a L : ℝ) (hL : 0≤L) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ‖iteratedDeriv n (fun s : ℝ=>gaussianFlow R (s:ℂ)) y‖≤C*R^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianFlow_disk_bound a L hL
  refine ⟨(n.factorial:ℝ)*B,by positivity,?_⟩
  intro R hR y hy
  rw [iteratedDeriv_restrict_real _ (fun x=>gaussianFlow_analytic R (x:ℂ)) n y]
  have hf : Differentiable ℂ (gaussianFlow R) := fun z=>(gaussianFlow_analytic R z).differentiableAt
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<1) hf.diffContOnCl
    (fun z hz=>hbound R hR y hy z (Metric.sphere_subset_closedBall hz))
  simpa only [one_pow,div_one,mul_assoc] using h

end SevenEighths.ProbePhysical
end

end OAI

end Source1360

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianLogWindow.lean; sha256: e508f509619ab460fd408a82752c3d2694af63fcc8e6a5ec01d9b31910945d02 -/
section Source1361
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open Filter Set MeasureTheory
namespace SevenEighths.ProbePhysical

lemma gaussianFlow_real_smooth (R : ℝ) : ContDiff ℝ ∞ (fun s : ℝ=>gaussianFlow R (s:ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  have hf : ContDiffAt ℂ ∞ (gaussianFlow R) (s:ℂ) := (gaussianFlow_analytic R _).contDiffAt
  exact (hf.restrict_scalars ℝ).comp s Complex.ofRealCLM.contDiff.contDiffAt

def gaussianLogWindow (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) : SchwartzMap ℝ ℂ :=
  (hV.mul_right (f':=fun s : ℝ=>gaussianFlow R (s:ℂ))).toSchwartzMap
    (V.smooth'.mul (gaussianFlow_real_smooth R))
@[simp] lemma gaussianLogWindow_apply (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (R s : ℝ) : gaussianLogWindow V hV R s=V s*gaussianFlow R (s:ℂ) := rfl

lemma gaussianLogWindow_derivative_outside (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hbox : ∀s,V s≠0→|s|≤L) (R y : ℝ) (hy : L < |y|) (n : ℕ) :
    iteratedDeriv n (gaussianLogWindow V hV R) y=0 := by
  have he : (gaussianLogWindow V hV R:ℝ→ℂ)=ᶠ[𝓝 y](fun _=>0) := by
    have hu : {x : ℝ | L < |x|}∈𝓝 y := (isOpen_lt continuous_const continuous_abs).mem_nhds hy
    filter_upwards [hu] with x hx
    have hv : V x=0 := by by_contra h; exact (not_lt_of_ge (hbox x h)) hx
    simp only [gaussianLogWindow_apply,hv,zero_mul]
  rw [he.iteratedDeriv_eq n]
  simp

lemma gaussianLogWindow_derivative_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ‖iteratedDeriv n (gaussianLogWindow V hV R) y‖≤C*R^(-a) := by
  choose B hB hbound using fun i : ℕ=>gaussianFlow_derivative_bound a L hL i
  let A (i : ℕ) := SchwartzMap.seminorm ℝ 0 i V
  let C := ∑i∈Finset.range (n+1),(n.choose i:ℝ)*A i*B (n-i)
  have hA (i : ℕ) : 0≤A i := apply_nonneg _ _
  have hC : 0≤C := Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _).le)
  refine ⟨C+1,by positivity,?_⟩
  intro R hR y hy
  change ‖iteratedDeriv n (fun s : ℝ=>V s*gaussianFlow R (s:ℂ)) y‖≤_
  rw [iteratedDeriv_fun_mul (f:=(V:ℝ→ℂ)) (g:=fun s : ℝ=>gaussianFlow R (s:ℂ))
    (V.smooth'.contDiffAt.of_le (by simp))
    ((gaussianFlow_real_smooth R).contDiffAt.of_le (by simp))]
  calc
    _ ≤ ∑i∈Finset.range (n+1),‖(n.choose i:ℂ)*iteratedDeriv i V y*
        iteratedDeriv (n-i) (fun s : ℝ=>gaussianFlow R (s:ℂ)) y‖ := norm_sum_le _ _
    _ ≤ ∑i∈Finset.range (n+1),((n.choose i:ℝ)*A i)*(B (n-i)*R^(-a)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      have hv : ‖iteratedDeriv i V y‖≤A i := by
        simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm' ℝ 0 i V y
      exact mul_le_mul (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _))
        (hbound _ R hR y hy) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
    _ = C*R^(-a) := by simp only [C,Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ (C+1)*R^(-a) := by nlinarith [Real.rpow_pos_of_pos hR (-a)]

theorem gaussianLogWindow_seminorm (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (hbox : ∀s,V s≠0→|s|≤L) (a : ℝ) (k n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
      SchwartzMap.seminorm ℝ k n (gaussianLogWindow V hV R)≤C*R^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianLogWindow_derivative_bound V hV L hL a n
  refine ⟨(1+L^k)*B,by positivity,?_⟩
  intro R hR
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro y
  by_cases hy : |y|≤L
  · calc
      _ ≤ L^k*(B*R^(-a)) := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hy k)
        (hbound R hR y hy) (norm_nonneg _) (pow_nonneg hL _)
      _ ≤ _ := by nlinarith [mul_pos hB (Real.rpow_pos_of_pos hR (-a))]
  · rw [gaussianLogWindow_derivative_outside V hV L hbox R y (lt_of_not_ge hy) n,norm_zero,mul_zero]
    positivity

theorem gaussianLogWindow_fourier_moment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (hbox : ∀s,V s≠0→|s|≤L) (a : ℝ) (J : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
      (∫t : ℝ,(1+‖t‖)^J*‖(𝓕 (gaussianLogWindow V hV R)) t‖)≤C*R^(-a) := by
  let p := (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower
  let K := J+p
  choose B hB hb using fun q : ℕ×ℕ=>gaussianLogWindow_seminorm V hV L hL hbox a q.1 q.2
  let C := (∑i∈Finset.range (K+1),(B (0,i)+B (p,i)))+1
  have hC : 0<C := by
    have hh : 0≤∑i∈Finset.range (K+1),(B (0,i)+B (p,i)) :=
      Finset.sum_nonneg (fun i _=>add_nonneg (hB _).le (hB _).le)
    dsimp only [C]; linarith
  let D := (2:ℝ)^J*(FourierBridge.coefficientMomentBound 0 C+FourierBridge.coefficientMomentBound J C)
  have hD : 0≤D := mul_nonneg (by positivity)
    (add_nonneg (FourierBridge.coefficientMomentBound_nonneg _ _ hC.le)
      (FourierBridge.coefficientMomentBound_nonneg _ _ hC.le))
  refine ⟨D+1,by positivity,?_⟩
  intro R hR
  have hcancel : R^a*R^(-a)=1 := by rw [←Real.rpow_add hR]; simp
  have hsource (i : ℕ) (hi : i≤J+(MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower) :
      R^a*(SchwartzMap.seminorm ℝ 0 i (gaussianLogWindow V hV R)+
        SchwartzMap.seminorm ℝ p i (gaussianLogWindow V hV R))≤C := by
    have hbi : B (0,i)+B (p,i)≤C := by
      have hh := Finset.single_le_sum (s:=Finset.range (K+1)) (a:=i)
        (f:=fun i=>B (0,i)+B (p,i))
        (fun i _=>add_nonneg (hB _).le (hB _).le) (Finset.mem_range.mpr (by dsimp only [K,p]; omega))
      dsimp only [C]; linarith
    calc
      _ ≤ R^a*(B (0,i)*R^(-a)+B (p,i)*R^(-a)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hb (0,i) R hR) (hb (p,i) R hR)) (by positivity)
      _ = B (0,i)+B (p,i) := by rw [←add_mul]; calc
        _=(B (0,i)+B (p,i))*(R^a*R^(-a)) := by ring
        _=_ := by rw [hcancel,mul_one]
      _ ≤ C := hbi
  have hh := FourierBridge.uniform_fourier_one_plus_moment (gaussianLogWindow V hV R) J
    (R^a) C (by positivity) hC.le hsource
  change R^a*(∫t : ℝ,(1+‖t‖)^J*‖(𝓕 (gaussianLogWindow V hV R)) t‖)≤D at hh
  have hp := mul_le_mul_of_nonneg_left hh (Real.rpow_pos_of_pos hR (-a)).le
  have hc' : R^(-a)*R^a=1 := by rw [mul_comm,hcancel]
  rw [←mul_assoc,hc',one_mul] at hp
  exact hp.trans (by nlinarith [Real.rpow_pos_of_pos hR (-a)])

end SevenEighths.ProbePhysical
end

end OAI

end Source1361

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianCoupled.lean; sha256: 21a6117120a386823e2f596b2b5e2e52e7cf4ffebddffac10de8ed320ba9cb5e -/
section Source1362
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set FourierBridge LocalLogFourier
namespace SevenEighths.ProbePhysical

def gaussianJointDensity (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) : SchwartzMap ℝ ℂ :=
  𝓕 (gaussianLogWindow V hV R)

lemma gaussianProfile_positive_smooth : ContDiffOn ℝ ∞ gaussianMellinProfile (Set.Ioi 0) := by
  intro y hy
  have hh := (gaussianProfile_scaled_smooth 1 (by norm_num) y hy).contDiffWithinAt (s:=Set.Ioi 0)
  simpa only [one_mul] using hh

lemma gaussianLogWindow_eq_positive (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (R : ℝ) (hR : 0<R) : gaussianLogWindow V hV R=
      positiveLogProfile V gaussianMellinProfile R hV V.smooth' gaussianProfile_positive_smooth hR := by
  ext s
  simp only [gaussianLogWindow_apply,positiveLogProfile_apply,gaussianFlow_real R hR]

theorem gaussian_coupled_separation {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (a y : ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) (hR : 0<R)
    (hactive : (∏i,W i (y i))≠0→V (∑i,a i*y i)=1) :
    (∏i,W i (y i))*gaussianMellinProfile (R*Real.exp (∑i,a i*y i))=
      ∫t : ℝ,(∏i,W i (y i)*logPhase t (a i*y i))*gaussianJointDensity V hV R t := by
  have hh := coupled_positive_log_separation W gaussianMellinProfile V R a y hV V.smooth'
    gaussianProfile_positive_smooth hR hactive
  rw [←gaussianLogWindow_eq_positive V hV R hR] at hh
  exact hh

theorem gaussian_coupled_family {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (a M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i y≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀R : ℝ,0<R→∀y : ι→ℝ,
        (∏i,W i (y i))*gaussianMellinProfile (R*Real.exp (∑i,a i*y i))=
          ∫t : ℝ,(∏i,W i (y i)*logPhase t (a i*y i))*gaussianJointDensity V hV R t) ∧
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤C*R^(-A)) := by
  let T := ∑i,|a i| *M i
  have hT : 0≤T := Finset.sum_nonneg (fun i _=>mul_nonneg (abs_nonneg _) (hM i))
  obtain ⟨φ,hφc,hφs,hφone,hφsupp,_⟩ := FourierBridge.exists_complex_smooth_cutoff T hT
  let V : SchwartzMap ℝ ℂ := hφc.toSchwartzMap hφs
  have hV : HasCompactSupport (V:ℝ→ℂ) := hφc
  have hbox : ∀s,V s≠0→|s|≤T+1 := by
    intro s hs
    have hh := hφsupp (subset_tsupport φ hs)
    exact abs_le.mpr hh
  refine ⟨V,hV,?_,?_⟩
  · intro R hR y
    apply gaussian_coupled_separation W a y V hV R hR
    exact FourierBridge.coupled_cutoff_active W φ a y M hwindow (by simpa only [T] using hφone)
  · intro A J
    obtain ⟨C,hC,hbound⟩ := gaussianLogWindow_fourier_moment V hV (T+1) (by linarith) hbox A J
    refine ⟨C,hC,?_⟩
    intro R hR
    exact ⟨JointLogSeparation.weighted_schwartz_integrable (gaussianJointDensity V hV R) J,hbound R hR⟩

end SevenEighths.ProbePhysical
end

end OAI

end Source1362

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianSlots.lean; sha256: fcf0dc45845a9cde9f15d3277b659811a20223d23b6277a193a42efc1dca1a09 -/
section Source1363
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical

def gaussianSlotWindow {ι : Type*} (W : ι→ℝ→ℂ) : Option ι→ℝ→ℂ
  | none => fun y=>gaussianAnnulus (Real.exp y)
  | some i => fun y=>W i (Real.exp y)
def gaussianSlotSlope {ι : Type*} : Option ι→ℝ
  | none => 1
  | some _ => -1
def gaussianSlotPoint {ι : Type*} (x : ℝ) (q : ι→ℝ) : Option ι→ℝ
  | none => Real.log x
  | some i => Real.log (q i)

lemma gaussianSlot_argument {ι : Type*} [Fintype ι] (x : ℝ) (hx : 0<x) (q : ι→ℝ) (hq : ∀i,0<q i) :
    Real.exp (∑i : Option ι,gaussianSlotSlope i*gaussianSlotPoint x q i)=x/(∏i,q i) := by
  simp only [Fintype.sum_option,gaussianSlotSlope,gaussianSlotPoint,one_mul,neg_one_mul]
  rw [Real.exp_add,Real.exp_sum,Real.exp_log hx]
  simp_rw [Real.exp_neg,Real.exp_log (hq _)]
  rw [Finset.prod_inv_distrib]
  rfl

lemma logPhase_neg_argument (t y : ℝ) : logPhase t (-y)=logPhase (-t) y := by
  unfold logPhase
  congr 1
  push_cast
  ring

lemma gaussianSlot_product {ι : Type*} [Fintype ι] (W : ι→ℝ→ℂ)
    (x : ℝ) (hx : 0<x) (q : ι→ℝ) (hq : ∀i,0<q i) (t : ℝ) :
    (∏i : Option ι,gaussianSlotWindow W i (gaussianSlotPoint x q i)*
      logPhase t (gaussianSlotSlope i*gaussianSlotPoint x q i))=
      gaussianAnnulus x*logPhase t (Real.log x)*
        ∏i,W i (q i)*logPhase (-t) (Real.log (q i)) := by
  simp only [Fintype.prod_option,gaussianSlotWindow,gaussianSlotPoint,gaussianSlotSlope,
    one_mul,neg_one_mul,Real.exp_log hx,logPhase_neg_argument]
  simp_rw [Real.exp_log (hq _)]

lemma gaussianFixedWindow_Vstar_twist (t x : ℝ) (hx : 0<x) :
    Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x=
      gaussianAnnulus x*logPhase t (Real.log x) := by
  have hs : (Real.sqrt x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
  unfold Vstar CompletedHeight.normTwistedSource gaussianFixedWindow
  field_simp

lemma gaussianAnnulus_log_support (y : ℝ) (hy : gaussianAnnulus (Real.exp y)≠0) :
    |y|≤|Real.log (1/2)|+|Real.log 2|+1 := by
  have hlo : (1/2:ℝ)<Real.exp y := by
    by_contra h; exact hy (gaussianAnnulus_small _ (le_of_not_gt h))
  have hhi : Real.exp y<2 := by
    by_contra h; exact hy (gaussianAnnulus_large _ (le_of_not_gt h))
  have hl : Real.log (1/2)≤y := by simpa using Real.log_le_log (by norm_num : (0:ℝ)<1/2) hlo.le
  have hh : y≤Real.log 2 := by simpa using Real.log_le_log (Real.exp_pos y) hhi.le
  rw [abs_le]
  constructor
  · have := neg_abs_le (Real.log (1/2)); have := abs_nonneg (Real.log 2); linarith
  · have := le_abs_self (Real.log 2); have := abs_nonneg (Real.log (1/2)); linarith

theorem gaussian_selected_slot_family {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
        gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
          ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
            (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t) ∧
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤C*R^(-A)) := by
  let M' : Option ι→ℝ := fun o=>match o with
    | none => |Real.log (1/2)|+|Real.log 2|+1
    | some i => M i
  have hM' : ∀o,0≤M' o := by intro o; cases o with
    | none => dsimp [M']; positivity
    | some i => exact hM i
  have hW : ∀o y,gaussianSlotWindow W o y≠0→|y|≤M' o := by
    intro o y
    cases o with
    | none => exact gaussianAnnulus_log_support y
    | some i => exact hwindow i y
  obtain ⟨V,hV,hsep,hbound⟩ := gaussian_coupled_family (gaussianSlotWindow W) gaussianSlotSlope M' hM' hW
  refine ⟨V,hV,?_,hbound⟩
  intro R hR x hx q hq
  have hh := hsep R hR (gaussianSlotPoint x q)
  rw [gaussianSlot_argument x hx q hq] at hh
  simp only [Fintype.prod_option,gaussianSlotWindow,gaussianSlotPoint,Real.exp_log hx] at hh
  simp_rw [Real.exp_log (hq _)] at hh
  rw [show R*(x/∏i,q i)=R*x/(∏i,q i) by ring] at hh
  rw [hh]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [gaussianFixedWindow_Vstar_twist t x hx]
  simp only [gaussianSlotSlope,one_mul,neg_one_mul,logPhase_neg_argument]

end SevenEighths.ProbePhysical
end

end OAI

end Source1363

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianCompletedSlots.lean; sha256: afa8f31c3a5d01b230b9f22547aa35057827a844f272753b395931d3b6efc006 -/
section Source1364
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma correctedSummand_normTwisted (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (W : ℝ→ℂ) (T t : ℝ) (I J : Id) :
    correctedSummand S D Ψ (CompletedHeight.normTwistedSource W t) T I J=
      logPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T))*
        correctedSummand S D Ψ W T I J := by
  unfold correctedSummand markedSummand CompletedGauss.summand Vstar
    CompletedHeight.normTwistedSource
  ring

lemma correctedSummand_fixed_finite (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (T : ℝ) (hT : 0<T) :
    (Function.support (fun p : Id×Id=>correctedSummand S D Ψ gaussianFixedWindow T p.1 p.2)).Finite := by
  apply (completedT_finite_support Ψ gaussianFixedWindow gaussianFixedWindow_compact T hT).subset
  intro p hp hz
  exact hp (by simp only [correctedSummand,markedSummand,hz,mul_zero])

lemma gaussian_slot_integrable {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (q : ι→ℝ) (b : SchwartzMap ℝ ℂ) (x : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ=>logPhase t x*c*
      (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*b t) := by
  have hh : Integrable (fun t : ℝ=>b t*(logPhase t x*c*
      ∏i,W i (q i)*logPhase (-t) (Real.log (q i)))) := by
    apply b.integrable.mul_bdd (c:=‖c‖*∏i,‖W i (q i)‖)
    · apply Continuous.aestronglyMeasurable
      apply Continuous.mul ((logPhase_continuous_left x).mul_const c)
      apply continuous_finsetProd
      intro i hi
      exact ((logPhase_continuous_left (Real.log (q i))).comp continuous_neg).const_mul _
    · apply Filter.Eventually.of_forall
      intro t
      simp only [norm_mul,norm_prod,logPhase_norm,mul_one,one_mul,le_refl]
  simpa only [mul_comm (b _) _] using hh

lemma gaussian_selected_summand {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (S : Finset Id) (D : Id) (Ψ : O→*ℂ) (Z : ℝ) (hZ : 0<Z) (j : ℕ)
    (q : ι→ℝ) (hq : ∀i,0<q i) (I J : Id) :
    (∏i,W i (q i))*correctedSummand S D Ψ
      (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j) I J=
      ∫t : ℝ,correctedSummand S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j) I J*
        (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  by_cases hI : I=0
  · subst I
    simp [correctedSummand,markedSummand,CompletedGauss.summand]
  by_cases hJ : J=0
  · subst J
    simp [correctedSummand,markedSummand,CompletedGauss.summand]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hT : (0:ℝ)<2^j := by positivity
  have hN := div_pos (mul_pos hi (pow_pos hj 3)) hT
  have hprod : 0<∏i,q i := Finset.prod_pos (fun i _=>hq i)
  have hh := hsep ((2:ℝ)^j/Z) (div_pos hT hZ) _ hN q hq
  have he : (2:ℝ)^j/Z*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/(∏i,q i)=
      (2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/(Z*∏i,q i) := by ring
  rw [he] at hh
  unfold correctedSummand markedSummand CompletedGauss.summand
  rw [gaussianDyadicProfile_Vstar _ _ _ hN]
  let c : ℂ := completedCorrection I J*completedMask S D I J*
    (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I):ℂ))*cubeWeight Ψ J
  calc
    _ = c*(gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
      (∏i,W i (q i))*gaussianMellinProfile
        ((2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/(Z*∏i,q i))) := by dsimp [c]; ring
    _ = c*∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t)
      ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
        (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by rw [hh]
    _ = _ := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp [c]
      ring

lemma correctedSummand_gaussian_factor (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (j : ℕ) (I J : Id) :
    correctedSummand S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) I J=
      gaussianMellinProfile (((2:ℝ)^j/Z)*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j))*
        correctedSummand S D Ψ gaussianFixedWindow ((2:ℝ)^j) I J := by
  rw [gaussianDyadicProfile_factor]
  unfold correctedSummand markedSummand CompletedGauss.summand Vstar
  ring

lemma gaussian_selected_completed_integrable {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (q : ι→ℝ) (b : SchwartzMap ℝ ℂ)
    (S : Finset Id) (D : Id) (Ψ : O→*ℂ) (T : ℝ) (hT : 0<T) :
    Integrable (fun t : ℝ=>correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
      (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*b t) := by
  let hf := correctedSummand_fixed_finite S D Ψ T hT
  have hz (p : Id×Id) (hp : p∉hf.toFinset) :
      correctedSummand S D Ψ gaussianFixedWindow T p.1 p.2=0 := by
    simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hp
  have hr (t : ℝ) : correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T=
      ∑p∈hf.toFinset,correctedSummand S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2 := by
    exact tsum_eq_sum (fun p hp=>by rw [correctedSummand_normTwisted,hz p hp,mul_zero])
  simp_rw [hr,Finset.sum_mul]
  apply integrable_finsetSum
  intro p hp
  simp_rw [correctedSummand_normTwisted]
  exact gaussian_slot_integrable W q b _ _

theorem gaussian_selected_completed {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (S : Finset Id) (D : Id) (Ψ : O→*ℂ) (Z : ℝ) (hZ : 0<Z) (j : ℕ)
    (q : ι→ℝ) (hq : ∀i,0<q i) :
    (∏i,W i (q i))*correctedCompletedT S D Ψ
      (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j)=
      ∫t : ℝ,correctedCompletedT S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  let hf := correctedSummand_fixed_finite S D Ψ ((2:ℝ)^j) (by positivity)
  have hz (p : Id×Id) (hp : p∉hf.toFinset) :
      correctedSummand S D Ψ gaussianFixedWindow ((2:ℝ)^j) p.1 p.2=0 := by
    simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hp
  have hl : correctedCompletedT S D Ψ (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j)=
      ∑p∈hf.toFinset,correctedSummand S D Ψ (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j) p.1 p.2 := by
    exact tsum_eq_sum (fun p hp=>by rw [correctedSummand_gaussian_factor,hz p hp,mul_zero])
  have hr (t : ℝ) : correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)=
      ∑p∈hf.toFinset,correctedSummand S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j) p.1 p.2 := by
    exact tsum_eq_sum (fun p hp=>by rw [correctedSummand_normTwisted,hz p hp,mul_zero])
  have hi (p : Id×Id) : Integrable (fun t : ℝ=>
      correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j) p.1 p.2*
        (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
    simp_rw [correctedSummand_normTwisted]
    exact gaussian_slot_integrable W q _ _ _
  rw [hl,Finset.mul_sum]
  simp_rw [hr,Finset.sum_mul]
  rw [integral_finsetSum _ (fun p _=>hi p)]
  apply Finset.sum_congr rfl
  intro p hp
  exact gaussian_selected_summand W V hV hsep S D Ψ Z hZ j q hq p.1 p.2

end SevenEighths.ProbePhysical
end

end OAI

end Source1364

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianTuple.lean; sha256: d25b42be81da032dedf63954f8cc203f9fedefc1c14e3fad6753216c475c7a7d -/
section Source1365
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gaussian_selected_tuple_sum {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (Z : ℝ) (hZ : 0<Z) (j : ℕ) (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0<q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j))=
      ∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  have hi (k : α) : Integrable (fun t : ℝ=>a k*correctedCompletedT S (D k) (Ψ k)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
    simpa only [mul_assoc] using (gaussian_selected_completed_integrable W (q k) _ S (D k) (Ψ k) _ (by positivity)).const_mul _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun k _=>hi k)]
  apply Finset.sum_congr rfl
  intro k hk
  have hh := gaussian_selected_completed W V hV hsep S (D k) (Ψ k) Z hZ j (q k) (hq k hk)
  calc
    _ = a k*((∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j)) := by ring
    _ = a k*∫t : ℝ,correctedCompletedT S (D k) (Ψ k)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
      (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i)))*
        gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by rw [hh]
    _ = _ := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t=>by dsimp only; ring)

lemma gaussian_selected_scale {ι : Type*} [Fintype ι]
    (Z : ℝ) (P Q : ι→ℝ) (hP : ∀i,0<P i) :
    (Z*∏i,P i)*(∏i,Q i/P i)=Z*∏i,Q i := by
  rw [Finset.prod_div_distrib]
  have hp : (∏i,P i)≠0 := ne_of_gt (Finset.prod_pos (fun i _=>hP i))
  field_simp

theorem gaussian_selected_tuple_family {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤C*R^(-A)) ∧
      (∀F : Finset α,∀a : α→ℂ,∀S : Finset Id,∀D : α→Id,∀Ψ : α→O→*ℂ,
        ∀Z : ℝ,0<Z→∀j : ℕ,∀q : α→ι→ℝ,(∀k∈F,∀i,0<q k i)→
        (∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
          (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j))=
          ∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
            (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
            (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
              gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
  obtain ⟨V,hV,hsep,hbound⟩ := gaussian_selected_slot_family W M hM hwindow
  exact ⟨V,hV,hbound,fun F a S D Ψ Z hZ j q hq=>
    gaussian_selected_tuple_sum W V hV hsep F a S D Ψ Z hZ j q hq⟩

lemma gaussianFixedWindow_twist_compact (t : ℝ) :
    HasCompactSupport (CompletedHeight.normTwistedSource gaussianFixedWindow t) := by
  exact gaussianFixedWindow_compact.mul_left

theorem gaussian_twisted_physical_row_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id) (j : ℕ) (t : ℝ) :
    correctedCompletedT S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist
            (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
              (calibrationLowData S hS) s hs χ)
            (calibrationForSet S hS).generator 1 z)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)
          (fun A=>if D∣A then (1:ℂ) else 0) := by
  exact correctedPhysicalRow_eq_periodic_inverse η S hS hbad s hs z D _
    (gaussianFixedWindow_twist_compact t) _ (by positivity) (calibrationLowData S hS)

lemma correctedGaussian_dyadic_summable (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0<Z) :
    Summable (fun j : ℕ=>correctedCompletedT S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j)) := by
  have hh := (annular_reassembly_summable
    (fun p : Id×Id=>correctedSummand S D Ψ gaussianCompletedProfile Z p.1 p.2)
    (fun p : Id×Id=>(Ideal.absNorm p.1:ℝ)*(Ideal.absNorm p.2:ℝ)^3)
    (gaussian_correctedSummand_summable S D Ψ hΨ Z hZ)
    (fun p=>gaussian_correctedSummand_norm_ge_one S D Ψ Z p.1 p.2)).prod_symm.prod
  simpa only [correctedCompletedT,gaussian_dyadic_correctedSummand S D Ψ Z hZ,Prod.swap] using hh

theorem gaussian_selected_tuple_reassembly {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (hΨ : ∀k∈F,∀n,‖Ψ k n‖≤1) (Z : ℝ) (hZ : 0<Z)
    (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0<q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      gaussianCompletedProfile (Z*∏i,q k i))=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  have hp (k : α) (hk : k∈F) : 0<Z*∏i,q k i :=
    mul_pos hZ (Finset.prod_pos (fun i _=>hq k hk i))
  have hd (k : α) (hk : k∈F) : Summable (fun j : ℕ=>a k*(∏i,W i (q k i))*
      correctedCompletedT S (D k) (Ψ k) (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j)) :=
    (correctedGaussian_dyadic_summable S (D k) (Ψ k) (hΨ k hk) _ (hp k hk)).mul_left _
  calc
    _ = ∑k∈F,∑'j : ℕ,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [correctedGaussian_eq_tsum_dyadic S (D k) (Ψ k) (hΨ k hk) _ (hp k hk),tsum_mul_left]
    _ = ∑'j : ℕ,∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j) := (Summable.tsum_finsetSum hd).symm
    _ = _ := by
      apply tsum_congr
      intro j
      exact gaussian_selected_tuple_sum W V hV hsep F a S D Ψ Z hZ j q hq

end SevenEighths.ProbePhysical
end

end OAI

end Source1365

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalRows.lean; sha256: 58b97cbec9cc8b7c8fdb1feaffd1b91f62e1e247bcbb57aa865750dad2c456c8 -/
section Source1366
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev PhysicalRowIndex := {I : Id // Supported I}×O

def physicalRowMonoid (η : HeckeFamily.Character) (C : CalibrationData) (r : PhysicalRowIndex) : O→*ℂ :=
  rowCoefficient η C.Xi (primaryGenerator r.1.val)
    ((supported_span_primaryGenerator_iff r.1.val).mpr r.1.property) r.2

def physicalRowWeight (C : CalibrationData) (W0 W1 : ℝ→ℂ) (X Y : ℝ) (r : PhysicalRowIndex) : ℂ :=
  if ∀P∈C.excluded,¬P∣r.1.val then
    let a := primaryGenerator r.1.val
    let ha := supported_primaryGenerator_ne_zero r.1.val r.1.property
    let q : ℝ := Ideal.absNorm r.1.val
    (Y:ℂ)⁻¹*W1 (q/Y)*CanonicalRowCompletion.idealRowHom C.generator r.1.val/
      (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q*X):ℂ))*
      C.residueMonoid r.2*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-r.2)*
        W0 (elementNorm r.2/(elementNorm C.generator*q*X))
  else 0

lemma physicalRowMonoid_norm (η : HeckeFamily.Character) (C : CalibrationData)
    (r : PhysicalRowIndex) (n : O) : ‖physicalRowMonoid η C r n‖≤1 :=
  rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ r.2 n

lemma physicalRowWeight_outer_zero (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) (h : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)=0) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  unfold physicalRowWeight
  split_ifs <;> simp [h]

lemma physicalRowWeight_inner_zero (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex)
    (h : W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))=0) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  unfold physicalRowWeight
  split_ifs <;> simp [h]

lemma physicalRowScale_pos (C : CalibrationData) (X : ℝ) (hX : 0<X)
    (s : {I : Id // Supported I}) : 0<elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X := by
  have hc : 0<elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hs : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  positivity

theorem physicalRowWeight_finite_support (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    (Function.support (physicalRowWeight C W0 W1 X Y)).Finite := by
  have ho := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  apply Set.Finite.of_finite_fibers Prod.fst
  · apply ho.subset
    rintro s ⟨r,hr,rfl⟩
    exact fun hz=>hr (physicalRowWeight_outer_zero C W0 W1 X Y r hz)
  · intro s hs
    have hm := elementWindow_finite_support W0 hW0 _ (physicalRowScale_pos C X hX s)
    apply ((Set.finite_singleton s).prod hm).subset
    intro r hr
    have he : r.1=s := hr.2
    refine ⟨he,?_⟩
    intro hz
    apply hr.1
    apply physicalRowWeight_inner_zero C W0 W1 X Y r
    simpa only [he] using hz

lemma physicalRowWeight_mul_summable (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (F : PhysicalRowIndex→ℂ) :
    Summable (fun r=>physicalRowWeight C W0 W1 X Y r*F r) := by
  apply summable_of_hasFiniteSupport
  apply (physicalRowWeight_finite_support C W0 W1 hW0 hW1 X Y hX hY).subset
  intro r hr hz
  exact hr (by dsimp only; rw [hz,zero_mul])

theorem markedPhysicalProbe_eq_rows (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (physicalRowMonoid η C r) t) := by
  have hf := physicalRowWeight_mul_summable C W0 W1 hW0 hW1 X Y hX hY
    (fun r=>verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (physicalRowMonoid η C r) t))
  rw [hf.tsum_prod]
  unfold markedPhysicalProbe
  rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  by_cases hc : ∀P∈C.excluded,¬P∣s.val
  · simp only [physicalRowWeight,physicalRowMonoid]
    try dsimp only
    simp only [ite_eq_left hc]
    rw [←tsum_mul_left,←tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  · simp only [physicalRowWeight]
    try dsimp only
    simp only [ite_eq_right hc,zero_mul,mul_zero,tsum_zero]

theorem markedPhysicalProbe_eq_gaussian_rows (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        correctedCompletedT C.excluded D (physicalRowMonoid η C r) gaussianCompletedProfile Z := by
  rw [markedPhysicalProbe_eq_rows η C D W0 W1 hW0 hW1 X Y Z hX hY]
  apply tsum_congr
  intro r
  rw [spectralRow_eq_gaussianCompleted _ _ _ (physicalRowMonoid_norm η C r) 4 (by norm_num) Z hZ]

end SevenEighths.ProbePhysical
end

end OAI

end Source1366

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowRay.lean; sha256: 4e5d316148776753dba3766095833f0565ad90d02c1ac31adf41dc10f9e718f4 -/
section Source1367
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open RayFourExpansion CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev PhysicalRayElement := {s : O // Supported (Ideal.span {s})}

def physicalRay (s : O) : RayRing := Ideal.Quotient.mk (Ideal.span {(4:O)}) s

def physicalRayRepresentative (σ : RayRing) : PhysicalRayElement :=
  if h : ∃s : PhysicalRayElement,physicalRay s.val=σ then Classical.choose h
  else ⟨1,by
    simp [Supported,Ideal.span_singleton_one,←Ideal.one_eq_top]
    change (1:Id)≠0
    exact one_ne_zero⟩

lemma physicalRayRepresentative_spec (s : PhysicalRayElement) :
    physicalRay (physicalRayRepresentative (physicalRay s.val)).val=physicalRay s.val := by
  have hh : ∃r : PhysicalRayElement,physicalRay r.val=physicalRay s.val := ⟨s,rfl⟩
  simp only [physicalRayRepresentative,dite_eq_left hh]
  exact Classical.choose_spec hh

lemma rowCoefficient_congr_ray (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s r : PhysicalRayElement) (h : physicalRay s.val=physicalRay r.val) (m : O) :
    rowCoefficient η Xi s.val s.property m=rowCoefficient η Xi r.val r.property m := by
  apply MonoidHom.ext
  intro n
  rw [rowCoefficient_apply,rowCoefficient_apply]
  have hd : (4:O)∣s.val-r.val := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have he : sexticReciprocityPhase s.val n=sexticReciprocityPhase r.val n := by
    unfold sexticReciprocityPhase
    rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub s.val r.val hd]
  rw [he]

def physicalRayRowMonoid (η : HeckeFamily.Character) (C : CalibrationData)
    (σ : RayRing) (m : O) : O→*ℂ :=
  rowCoefficient η C.Xi (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m

def physicalIdealRay (s : {I : Id // Supported I}) : RayRing := physicalRay (primaryGenerator s.val)

lemma physicalRowMonoid_eq_ray (η : HeckeFamily.Character) (C : CalibrationData) (r : PhysicalRowIndex) :
    physicalRowMonoid η C r=physicalRayRowMonoid η C (physicalIdealRay r.1) r.2 := by
  let s : PhysicalRayElement :=
    ⟨primaryGenerator r.1.val,(supported_span_primaryGenerator_iff r.1.val).mpr r.1.property⟩
  exact rowCoefficient_congr_ray η C.Xi s (physicalRayRepresentative (physicalRay s.val))
    (physicalRayRepresentative_spec s).symm r.2

lemma physicalRayRowMonoid_norm (η : HeckeFamily.Character) (C : CalibrationData)
    (σ : RayRing) (m n : O) : ‖physicalRayRowMonoid η C σ m n‖≤1 :=
  rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ m n

def physicalRayPeriodicBase (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) : O→*ℂ :=
  lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS) (physicalRayRepresentative σ).val
      (physicalRayRepresentative σ).property χ

theorem physicalRayPeriodicBase_uniform (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) :
    ∃L : Id,L≠0 ∧ ∀σ : RayRing,∀χ : RayCharacter,
      FactorsModulo L (physicalRayPeriodicBase η S hS σ χ) ∧
      ∀n : O,‖physicalRayPeriodicBase η S hS σ χ n‖≤1 := by
  refine ⟨lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS),
    lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _,?_⟩
  intro σ χ
  exact ⟨lowPeriodicBase_periodic η _ _ _ _ _ χ,lowPeriodicBase_norm η _ _ _ _ _ χ⟩

theorem physicalRayRow_eq_periodic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (σ : RayRing) (m : O) (D : Id) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (T : ℝ) (hT : 0<T) :
    correctedCompletedT S D (physicalRayRowMonoid η (calibrationForSet S hS) σ m) W T=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator 1 m)
          W T (fun A=>if D∣A then (1:ℂ) else 0) :=
  correctedPhysicalRow_eq_periodic_inverse η S hS hbad
    (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m D W hW T hT
      (calibrationLowData S hS)

end SevenEighths.ProbePhysical
end

end OAI

end Source1367

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowCutoff.lean; sha256: 18c6ab998cde0bd7761495a80b36fe77f0becc2a4d3b7b00b36a7e1e626baf0c -/
section Source1368
namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

def lowOuterCutoff (a b x : ℝ) : ℂ :=
  (Real.smoothTransition (2*x/a-1):ℂ)*(Real.smoothTransition (2-x/b):ℂ)

lemma lowOuterCutoff_small (a b : ℝ) (ha : 0<a) (x : ℝ) (hx : x≤a/2) :
    lowOuterCutoff a b x=0 := by
  have h : 2*x/a-1≤0 := by
    have hh : 2*x/a≤1 := (div_le_iff₀ ha).mpr (by linarith)
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.zero_of_nonpos h,Complex.ofReal_zero,zero_mul]

lemma lowOuterCutoff_large (a b : ℝ) (hb : 0<b) (x : ℝ) (hx : 2*b≤x) :
    lowOuterCutoff a b x=0 := by
  have h : 2-x/b≤0 := by
    have hh : 2≤x/b := (le_div_iff₀ hb).mpr hx
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.zero_of_nonpos h,Complex.ofReal_zero,mul_zero]

lemma lowOuterCutoff_one (a b : ℝ) (ha : 0<a) (hb : 0<b) (x : ℝ) (hlo : a≤x) (hhi : x≤b) :
    lowOuterCutoff a b x=1 := by
  have hl : 1≤2*x/a-1 := by
    have hh : 2≤2*x/a := (le_div_iff₀ ha).mpr (by linarith)
    linarith
  have hr : 1≤2-x/b := by
    have hh : x/b≤1 := (div_le_iff₀ hb).mpr (by simpa using hhi)
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.one_of_one_le hl,
    Real.smoothTransition.one_of_one_le hr,Complex.ofReal_one,mul_one]

lemma lowOuterCutoff_smooth (a b : ℝ) : ContDiff ℝ ∞ (lowOuterCutoff a b) := by
  unfold lowOuterCutoff
  exact (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))).mul
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop)))

lemma lowOuterCutoff_support (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Function.support (lowOuterCutoff a b)⊆Set.Icc (a/2) (2*b) := by
  intro x hx
  constructor
  · by_contra hh
    exact hx (lowOuterCutoff_small a b ha x (le_of_lt (lt_of_not_ge hh)))
  · by_contra hh
    exact hx (lowOuterCutoff_large a b hb x (le_of_lt (lt_of_not_ge hh)))

lemma lowOuterCutoff_compact (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    HasCompactSupport (lowOuterCutoff a b) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (lowOuterCutoff_support a b ha hb)

lemma physical_ratio_factor (B q X Y m : ℝ) (hq : 0<q) (hY : 0<Y) :
    m/(B*X*Y)=(q/Y)*(m/(B*q*X)) := by
  field_simp

lemma physical_window_cutoff_one (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (B q X Y m : ℝ) (hq : 0<q) (hY : 0<Y)
    (h0 : W0 (m/(B*q*X))≠0) (h1 : W1 (q/Y)≠0) :
    lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (m/(B*X*Y))=1 := by
  have h0b := hW0 h0
  have h1b := hW1 h1
  apply lowOuterCutoff_one _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  · rw [physical_ratio_factor B q X Y m hq hY]
    have hh := mul_le_mul h0b.1 h1b.1 ha1.le (le_trans ha0.le h0b.1)
    simpa only [mul_comm] using hh
  · rw [physical_ratio_factor B q X Y m hq hY]
    have hh := mul_le_mul h0b.2 h1b.2 (le_trans ha1.le h1b.1) (le_trans ha0.le (h0b.1.trans h0b.2))
    have hd : (q/Y)*(m/(B*q*X))≤b0*b1 := by simpa only [mul_comm] using hh
    exact hd.trans (le_max_right _ _)

theorem physicalRowWeight_insert_cutoff (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y : ℝ) (hY : 0<Y) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (elementNorm r.2/(elementNorm C.generator*X*Y))*
        physicalRowWeight C W0 W1 X Y r := by
  by_cases hz : physicalRowWeight C W0 W1 X Y r=0
  · simp only [hz,mul_zero]
  have h0 : W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))≠0 :=
    fun h=>hz (physicalRowWeight_inner_zero C W0 W1 X Y r h)
  have h1 : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)≠0 :=
    fun h=>hz (physicalRowWeight_outer_zero C W0 W1 X Y r h)
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  rw [physical_window_cutoff_one W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (elementNorm C.generator) (Ideal.absNorm r.1.val) X Y (elementNorm r.2) hq hY h0 h1,one_mul]

end SevenEighths.ProbePhysical
end

end OAI

end Source1368

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowMellin.lean; sha256: bef0d8a8c81e1b17beab5e079039a72c6d8c866aba61a5d068be095ee5ce3c27 -/
section Source1369
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical

lemma low_mellin_phase_norm (a v : ℝ) (ha : 0<a) :
    ‖(a:ℂ)^((v:ℂ)*Complex.I)‖=1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha]
  simp

lemma low_mellin_ratio_integrable (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Integrable (fun v : ℝ=>(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)*
      mellin W ((v:ℂ)*Complex.I)) := by
  have hm : Integrable (fun v : ℝ=>mellin W ((v:ℂ)*Complex.I)) := by
    have hh := compactMellin_vertical_integrable W a0 b0 ha0 hW hWs 0
    change Integrable (fun v : ℝ=>mellin W ((0:ℂ)+v*Complex.I)) at hh
    simpa using hh
  have hc : Continuous (fun v : ℝ=>(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne')))
  have hp : ∀v : ℝ,‖(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)‖≤1 := by
    intro v
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ha,Complex.norm_cpow_eq_rpow_re_of_pos hb]
    simp
  simpa only [mul_comm] using hm.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hp)

lemma low_mellin_ratio (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    W (a/b)=(1/(2*Real.pi):ℂ)*∫v : ℝ,
      (a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I) := by
  rw [compactMellin_inversion W a0 b0 ha0 hW hWs 0 _ (div_pos ha hb)]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  rw [Complex.ofReal_zero,zero_add,Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg ha.le hb.le]
  simp only [div_eq_mul_inv,←Complex.cpow_neg,neg_neg]

lemma low_sqrt_ratio (B q X Y : ℝ) (hB : 0<B) (hq : 0<q) (hX : 0<X) (hY : 0<Y) :
    (Real.sqrt (B*q*X):ℂ)⁻¹=
      (Real.sqrt (B*X*Y):ℂ)⁻¹*((q/Y:ℝ):ℂ)^(-(1/2:ℂ)) := by
  have hQ : 0<B*X*Y := by positivity
  have hb : 0<q/Y := div_pos hq hY
  have he : B*q*X=(B*X*Y)*(q/Y) := by field_simp
  rw [he,Real.sqrt_mul hQ.le,Complex.ofReal_mul,Complex.cpow_neg,ProbeEuler.cpow_half_eq_sqrt _ hb.le]
  simp only [mul_inv_rev,mul_comm]

theorem physical_radial_low_mellin (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (B q X Y m : ℝ) (hB : 0<B) (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hm : 0<m) :
    (Real.sqrt (B*q*X):ℂ)⁻¹*W (m/(B*q*X))=
      (Real.sqrt (B*X*Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
          ((q/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I) := by
  have hQ : 0<B*X*Y := by positivity
  have ha : 0<m/(B*X*Y) := div_pos hm hQ
  have hb : 0<q/Y := div_pos hq hY
  have hbc : ((q/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have he : m/(B*q*X)=(m/(B*X*Y))/(q/Y) := by field_simp
  rw [he,low_mellin_ratio W a0 b0 ha0 hW hWs _ _ ha hb,low_sqrt_ratio B q X Y hB hq hX hY]
  simp_rw [Complex.cpow_add _ _ hbc]
  rw [show (fun v : ℝ=>((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
    (((q/Y:ℝ):ℂ)^(-(1/2:ℂ))*((q/Y:ℝ):ℂ)^((v:ℂ)*Complex.I))*mellin W ((v:ℂ)*Complex.I))=
    (fun v : ℝ=>((q/Y:ℝ):ℂ)^(-(1/2:ℂ))*
      (((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*((q/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I))) by funext v; ring]
  rw [integral_const_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1369

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowRowMellin.lean; sha256: 485c4c24852590e61653d2639d777d7e65f90627b937d93e26ce5bf722019799 -/
section Source1370
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowAdditiveCoefficient (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) : ℂ :=
  if ∀P∈C.excluded,¬P∣s.val then
    let a := primaryGenerator s.val
    let ha := supported_primaryGenerator_ne_zero s.val s.property
    let q : ℝ := Ideal.absNorm s.val
    (Y:ℂ)⁻¹*W1 (q/Y)*idealRowHom C.generator s.val/(C.tau*C.residueMonoid a)*
      ((q/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-m)
  else 0

def lowPhysicalScale (C : CalibrationData) (X Y : ℝ) : ℝ := elementNorm C.generator*X*Y

def lowRowMellinIntegrand (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) (v : ℝ) : ℂ :=
  mellin W0 ((v:ℂ)*Complex.I)*Ω (elementNorm r.2/lowPhysicalScale C X Y)*C.residueMonoid r.2*
    ((elementNorm r.2/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
      lowAdditiveCoefficient C W1 Y r.1 r.2 v

lemma calibration_elementNorm_pos (C : CalibrationData) : 0<elementNorm C.generator := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))

lemma lowPhysicalScale_pos (C : CalibrationData) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    0<lowPhysicalScale C X Y := mul_pos (mul_pos (calibration_elementNorm_pos C) hX) hY

lemma lowAdditiveCoefficient_outer_zero (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) (h : W1 ((Ideal.absNorm s.val:ℝ)/Y)=0) :
    lowAdditiveCoefficient C W1 Y s m v=0 := by
  unfold lowAdditiveCoefficient
  split_ifs <;> simp [h]

lemma lowRowMellinIntegrand_nonzero_form (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (hY : 0<Y) (r : PhysicalRowIndex) (v : ℝ)
    (hc : ∀P∈C.excluded,¬P∣r.1.val) :
    lowRowMellinIntegrand C W0 W1 Ω X Y r v=
      ((Y:ℂ)⁻¹*W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*idealRowHom C.generator r.1.val/
        (C.tau*C.residueMonoid (primaryGenerator r.1.val))*
          (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ))*
          (Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
          sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)*
          Ω (elementNorm r.2/lowPhysicalScale C X Y)*C.residueMonoid r.2)*
        (((elementNorm r.2/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
          (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*mellin W0 ((v:ℂ)*Complex.I)) := by
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  have hqc : (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (div_pos hq hY).ne'
  unfold lowRowMellinIntegrand lowAdditiveCoefficient
  rw [ite_eq_left hc]
  dsimp only
  rw [Complex.cpow_add _ _ hqc]
  ring

lemma lowRowMellinIntegrand_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hΩ : Ω 0=0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (r : PhysicalRowIndex) : Integrable (lowRowMellinIntegrand C W0 W1 Ω X Y r) := by
  by_cases hm : r.2=0
  · have he : lowRowMellinIntegrand C W0 W1 Ω X Y r=0 := by
      funext v
      simp [lowRowMellinIntegrand,hm,elementNorm,hΩ]
    rw [he]
    exact integrable_zero _ _ _
  by_cases hc : ∀P∈C.excluded,¬P∣r.1.val
  · have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
    have hmpos : 0<elementNorm r.2 := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
    change Integrable (fun v : ℝ=>lowRowMellinIntegrand C W0 W1 Ω X Y r v)
    simp_rw [lowRowMellinIntegrand_nonzero_form C W0 W1 Ω X Y hY r _ hc]
    exact (low_mellin_ratio_integrable W0 a0 b0 ha0 hW0 hWs _ _
      (div_pos hmpos (lowPhysicalScale_pos C X Y hX hY)) (div_pos hq hY)).const_mul _
  · have he : lowRowMellinIntegrand C W0 W1 Ω X Y r=0 := by
      funext v
      simp [lowRowMellinIntegrand,lowAdditiveCoefficient,hc]
    rw [he]
    exact integrable_zero _ _ _

theorem physicalRowWeight_low_mellin (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowRowMellinIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y r v := by
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  have hΩ : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  by_cases hm : r.2=0
  · have hw : W0 0=0 := by
      by_contra hh
      have hx := (hW0 hh).1
      linarith
    simp [physicalRowWeight,lowRowMellinIntegrand,hm,elementNorm,hw,hΩ,Ω]
  by_cases hc : ∀P∈C.excluded,¬P∣r.1.val
  · have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
    have hmpos : 0<elementNorm r.2 := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
    rw [physicalRowWeight_insert_cutoff C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hY r]
    unfold physicalRowWeight lowRowMellinIntegrand lowAdditiveCoefficient lowPhysicalScale
    dsimp only
    simp only [ite_eq_left hc]
    have hh := physical_radial_low_mellin W0 a0 b0 ha0 hW0 hWs
      (elementNorm C.generator) (Ideal.absNorm r.1.val) X Y (elementNorm r.2)
      (calibration_elementNorm_pos C) hq hX hY hmpos

    calc
      _ = (Ω (elementNorm r.2/(elementNorm C.generator*X*Y))*(Y:ℂ)⁻¹*
        W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*idealRowHom C.generator r.1.val*
        (C.tau*C.residueMonoid (primaryGenerator r.1.val))⁻¹*C.residueMonoid r.2*
        (Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
        sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2))*
        ((Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X):ℂ)⁻¹*
          W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))) := by dsimp only [Ω]; simp only [div_eq_mul_inv,mul_inv_rev]; ring
      _ = _ := by
        rw [hh]
        repeat rw [←integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun v=>by dsimp only [Ω]; ring)
  · simp [physicalRowWeight,lowRowMellinIntegrand,lowAdditiveCoefficient,hc]

lemma lowAdditiveCoefficient_height (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ) (hY : 0<Y)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) :
    lowAdditiveCoefficient C W1 Y s m v=
      (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*lowAdditiveCoefficient C W1 Y s m 0 := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  have hqc : (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (div_pos hq hY).ne'
  unfold lowAdditiveCoefficient
  split_ifs
  · dsimp only
    rw [Complex.cpow_add _ _ hqc]
    simp only [Complex.ofReal_zero,zero_mul,add_zero]
    ring
  · simp

lemma lowAdditiveCoefficient_height_norm (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ) (hY : 0<Y)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) :
    ‖lowAdditiveCoefficient C W1 Y s m v‖=‖lowAdditiveCoefficient C W1 Y s m 0‖ := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  rw [lowAdditiveCoefficient_height C W1 Y hY s m v,norm_mul,
    low_mellin_phase_norm _ v (div_pos hq hY),one_mul]

def lowArithmeticCoefficient (C : CalibrationData) (s : {I : Id // Supported I}) : ℂ :=
  if ∀P∈C.excluded,¬P∣s.val then
    idealRowHom C.generator s.val/(C.tau*C.residueMonoid (primaryGenerator s.val))
  else 0

lemma calibration_residue_inverse_norm (C : CalibrationData) (a : O) : ‖(C.residueMonoid a)⁻¹‖≤1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero)
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  change ‖(C.residue (Ideal.Quotient.mk (Ideal.span {C.generator}) a))⁻¹‖≤1
  simpa only [MulChar.inv_apply_eq_inv'] using
    FiniteRayExpansion.norm_char_le_one C.residue⁻¹ (Ideal.Quotient.mk (Ideal.span {C.generator}) a)

lemma lowArithmeticCoefficient_norm (C : CalibrationData) (s : {I : Id // Supported I}) :
    ‖lowArithmeticCoefficient C s‖≤‖C.tau‖⁻¹ := by
  unfold lowArithmeticCoefficient
  split_ifs
  · simp only [div_eq_mul_inv,mul_inv_rev,norm_mul,norm_inv]
    have hi := calibration_residue_inverse_norm C (primaryGenerator s.val)
    rw [norm_inv] at hi
    have hh := (mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg _)) (idealRowHom_norm C.generator s.val)).trans hi
    simpa only [mul_assoc] using mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg C.tau)) hh
  · simp

lemma lowArithmeticCoefficient_source_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (s : {I : Id // Supported I}) : ‖lowArithmeticCoefficient (calibrationForSet S hS) s‖≤1 := by
  simpa only [calibrationForSet_tau_norm,inv_one] using lowArithmeticCoefficient_norm (calibrationForSet S hS) s

lemma lowAdditiveCoefficient_eq (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) :
    lowAdditiveCoefficient C W1 Y s m v=
      (Y:ℂ)⁻¹*W1 ((Ideal.absNorm s.val:ℝ)/Y)*lowArithmeticCoefficient C s*
        (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*
          (Real.sqrt (Ideal.absNorm s.val):ℂ)⁻¹*
            sexticGauss (primaryGenerator s.val) (supported_primaryGenerator_ne_zero s.val s.property) (-m) := by
  unfold lowAdditiveCoefficient lowArithmeticCoefficient
  split_ifs <;> simp only [mul_zero,zero_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1370

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowMellinFubini.lean; sha256: 4035f4dc914b859f298ed9cdc73428b17eac3e8da7229e24357ada789f837ee0 -/
section Source1371
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowRowMellinIntegrand_common_support (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    ∃R : Finset PhysicalRowIndex,∀v : ℝ,∀r∉R,
      lowRowMellinIntegrand C W0 W1 Ω X Y r v=0 := by
  have hs := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  have hm := elementWindow_finite_support Ω hΩ _ (lowPhysicalScale_pos C X Y hX hY)
  refine ⟨hs.toFinset×ˢhm.toFinset,?_⟩
  intro v r hr
  simp only [Finset.mem_product,Set.Finite.mem_toFinset,Set.mem_preimage,Function.mem_support] at hr
  by_cases h : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)=0
  · unfold lowRowMellinIntegrand
    rw [lowAdditiveCoefficient_outer_zero C W1 Y r.1 r.2 v h,mul_zero]
  · have ho : Ω (elementNorm r.2/lowPhysicalScale C X Y)=0 := by
      by_contra ho
      exact hr ⟨h,ho⟩
    simp [lowRowMellinIntegrand,ho]

lemma lowRowMellinIntegrand_mul_summable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (v : ℝ) (B : PhysicalRowIndex→ℂ) :
    Summable (fun r=>lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r) := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  apply summable_of_ne_finset_zero (s:=R)
  intro r hr
  rw [hR v r hr,zero_mul]

lemma lowRowMellinIntegrand_sum_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    Integrable (fun v : ℝ=>∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r) := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  have he (v : ℝ) : (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∑r∈R,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
    apply tsum_eq_sum
    intro r hr
    rw [hR v r hr,zero_mul]
  simp_rw [he]
  exact integrable_finsetSum R (fun r _=>(lowRowMellinIntegrand_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hΩ0 X Y hX hY r).mul_const _)

lemma lowRowMellinIntegrand_tsum_integral (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    (∑'r : PhysicalRowIndex,∫v : ℝ,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∫v : ℝ,∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  have he (v : ℝ) : (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∑r∈R,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
    apply tsum_eq_sum
    intro r hr
    rw [hR v r hr,zero_mul]
  rw [tsum_eq_sum (s:=R) (fun r hr=>by simp only [hR _ r hr,zero_mul,integral_zero])]
  simp_rw [he]
  exact (integral_finsetSum R (fun r _=>(lowRowMellinIntegrand_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hΩ0 X Y hX hY r).mul_const _)).symm

theorem physicalRowWeight_tsum_low_mellin (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*B r)=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,∑'r : PhysicalRowIndex,
          lowRowMellinIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y r v*B r := by
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  have hΩ : HasCompactSupport Ω := lowOuterCutoff_compact _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hΩ0 : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  simp_rw [physicalRowWeight_low_mellin C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY]
  simp_rw [mul_assoc,←integral_mul_const]
  repeat rw [tsum_mul_left]
  congr 2
  exact lowRowMellinIntegrand_tsum_integral C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1c hΩ hΩ0 X Y hX hY B

end SevenEighths.ProbePhysical
end

end OAI

end Source1371

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowRayAmplitude.lean; sha256: 7c2aedb44bc9cf4048d6a788d992168443a27b58e73e16160d5f50db0c1547d4 -/
section Source1372
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowRayAmplitude (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (m : O) (v : ℝ) : ℂ :=
  ∑'s : {I : Id // Supported I},if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0

lemma lowAdditiveCoefficient_common_support (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀m : O,∀v : ℝ,∀s∉F,
      lowAdditiveCoefficient C W1 Y s m v=0 := by
  have ho := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  refine ⟨ho.toFinset,?_⟩
  intro m v s hs
  apply lowAdditiveCoefficient_outer_zero
  simpa only [Set.Finite.mem_toFinset,Set.mem_preimage,Function.mem_support,not_not] using hs

lemma lowAdditiveCoefficient_mul_summable (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (m : O) (v : ℝ)
    (F : {I : Id // Supported I}→ℂ) :
    Summable (fun s=>lowAdditiveCoefficient C W1 Y s m v*F s) := by
  obtain ⟨R,hR⟩ := lowAdditiveCoefficient_common_support C W1 hW1 Y hY
  apply summable_of_ne_finset_zero (s:=R)
  intro s hs
  rw [hR m v s hs,zero_mul]

lemma lowRayAmplitude_eq_finite (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀σ : RayRing,∀m : O,∀v : ℝ,
      lowRayAmplitude C W1 Y σ m v=
        ∑s∈F,if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0 := by
  obtain ⟨F,hF⟩ := lowAdditiveCoefficient_common_support C W1 hW1 Y hY
  refine ⟨F,?_⟩
  intro σ m v
  apply tsum_eq_sum
  intro s hs
  simp only [hF m v s hs,ite_self]

lemma lowRayAmplitude_group (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (m : O) (v : ℝ)
    (B : RayRing→ℂ) :
    (∑'s : {I : Id // Supported I},lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s))=
      ∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ := by
  obtain ⟨F,hF⟩ := lowAdditiveCoefficient_common_support C W1 hW1 Y hY
  have hleft : (∑'s : {I : Id // Supported I},lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s))=
      ∑s∈F,lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s) := by
    apply tsum_eq_sum
    intro s hs
    rw [hF m v s hs,zero_mul]
  have hr (σ : RayRing) : lowRayAmplitude C W1 Y σ m v=
      ∑s∈F,if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0 := by
    apply tsum_eq_sum
    intro s hs
    simp only [hF m v s hs,ite_self]
  rw [hleft]
  simp_rw [hr,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [ite_mul,zero_mul]
  simp

end SevenEighths.ProbePhysical
end

end OAI

end Source1372

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowSeparated.lean; sha256: 0cd344ff44c0b4db181ba658a3589a4368cfdae6d4205a439b7204e60dda18b2 -/
section Source1373
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowSeparatedIntegrand (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (B : RayRing→O→ℂ) (v : ℝ) : ℂ :=
  mellin W0 ((v:ℂ)*Complex.I)*
    ∑'m : O,Ω (elementNorm m/lowPhysicalScale C X Y)*C.residueMonoid m*
      ((elementNorm m/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
        ∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ m

lemma lowSeparatedIntegrand_eq (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) (v : ℝ) :
    (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B (physicalIdealRay r.1) r.2)=
      lowSeparatedIntegrand C W0 W1 Ω X Y B v := by
  have hs := lowRowMellinIntegrand_mul_summable C W0 W1 Ω hW1 hΩ X Y hX hY v
    (fun r=>B (physicalIdealRay r.1) r.2)
  rw [hs.tsum_prod,←hs.tsum_comm]
  unfold lowSeparatedIntegrand
  rw [←tsum_mul_left]
  apply tsum_congr
  intro m
  rw [←lowRayAmplitude_group C W1 hW1 Y hY m v (fun σ=>B σ m)]
  repeat rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  unfold lowRowMellinIntegrand
  ring

lemma lowSeparatedIntegrand_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) :
    Integrable (lowSeparatedIntegrand C W0 W1 Ω X Y B) := by
  have hh := lowRowMellinIntegrand_sum_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1 hΩ hΩ0 X Y hX hY
    (fun r=>B (physicalIdealRay r.1) r.2)
  simpa only [lowSeparatedIntegrand_eq C W0 W1 Ω hW1 hΩ X Y hX hY B] using hh

theorem physicalRowWeight_low_separated (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) :
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*B (physicalIdealRay r.1) r.2)=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y B v := by
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  have hΩ := lowOuterCutoff_compact (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  rw [physicalRowWeight_tsum_low_mellin C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY]
  simp_rw [lowSeparatedIntegrand_eq C W0 W1 _ hW1c hΩ X Y hX hY B]

theorem markedPhysicalProbe_low_separated (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y
          (fun σ m=>correctedCompletedT C.excluded D (physicalRayRowMonoid η C σ m) gaussianCompletedProfile Z) v := by
  have hW0c : HasCompactSupport W0 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  rw [markedPhysicalProbe_eq_gaussian_rows η C D W0 W1 hW0c hW1c X Y Z hX hY hZ]
  simp_rw [physicalRowMonoid_eq_ray]
  exact physicalRowWeight_low_separated C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY
    (fun σ m=>correctedCompletedT C.excluded D (physicalRayRowMonoid η C σ m) gaussianCompletedProfile Z)

end SevenEighths.ProbePhysical
end

end OAI

end Source1373

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianDensityBudget.lean; sha256: 42ee10381da1a2003fe309f4b7773c4908bc625eff31f9c23392f82836ba9730 -/
section Source1374
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianJointMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (R : ℝ) : ℝ :=
  ∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖

lemma gaussianJointMoment_nonneg (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (R : ℝ) : 0≤gaussianJointMoment V hV J R := by
  apply integral_nonneg
  intro t
  positivity

lemma gaussianJointMoment_power_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (A : ℝ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→gaussianJointMoment V hV J R≤C*R^(-A) := by
  obtain ⟨L,hL,hbox⟩ := hV.isBounded.exists_pos_norm_le
  have hb : ∀s,V s≠0→|s|≤L := by
    intro s hs
    simpa only [Real.norm_eq_abs] using hbox s (subset_tsupport V hs)
  exact gaussianLogWindow_fourier_moment V hV L hL.le hb A J

lemma gaussianJointMoment_polynomial_decay (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J N : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→gaussianJointMoment V hV J R≤C/(1+R)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianJointMoment_power_bound V hV J 0
  obtain ⟨C,hC,hdecay⟩ := gaussianJointMoment_power_bound V hV J (N:ℝ)
  refine ⟨(B+C)*(2:ℝ)^N,by positivity,?_⟩
  intro R hR
  have hden : 0<(1+R)^N := pow_pos (by linarith) _
  by_cases hr1 : R≤1
  · have hh := hzero R hR
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2:ℝ)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb := mul_le_mul_of_nonneg_left hp hB.le
    nlinarith [mul_nonneg hC.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)]
  · have hh := hdecay R hR
    rw [Real.rpow_neg hR.le,Real.rpow_natCast] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2*R)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hm := mul_le_mul_of_nonneg_left hp (show 0≤C*(R^N)⁻¹ by positivity)
    rw [mul_pow] at hm
    have hn : R^N≠0 := ne_of_gt (pow_pos hR _)
    have he : (C*(R^N)⁻¹)*((2:ℝ)^N*R^N)=C*(2:ℝ)^N := by field_simp
    rw [he] at hm
    exact hm.trans (by nlinarith [mul_nonneg hB.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)])

theorem gaussianJointMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,0<Z→
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z))≤C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianJointMoment_polynomial_decay V hV J N
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound ((2:ℝ)^j/Z) (div_pos (by positivity) hZ))
      (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z) :=
    mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s) (gaussianJointMoment_nonneg V hV J _)
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1374

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianPhysicalTuple.lean; sha256: 2cb103c746aab311d4047d6e06950828d709e7564a34d0f7f56e52d193725d3b -/
section Source1375
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalRows_common_finset {α : Type*} (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (X Y : α→ℝ) (hX : ∀k∈F,0<X k) (hY : ∀k∈F,0<Y k) :
    ∃R : Finset PhysicalRowIndex,∀k∈F,∀r,r∉R→physicalRowWeight C W0 W1 (X k) (Y k) r=0 := by
  have hf (k : {k // k∈F}) := physicalRowWeight_finite_support C W0 W1 hW0 hW1
    (X k.val) (Y k.val) (hX k.val k.property) (hY k.val k.property)
  let R := F.attach.biUnion (fun k=>(hf k).toFinset)
  refine ⟨R,?_⟩
  intro k hk r hr
  by_contra hn
  apply hr
  exact Finset.mem_biUnion.mpr ⟨⟨k,hk⟩,by simp,by simpa only [Set.Finite.mem_toFinset,Function.mem_support] using hn⟩

theorem physical_selected_gaussian_reassembly {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (a : α→ℂ) (D : α→Id) (X Y : α→ℝ)
    (hX : ∀k∈F,0<X k) (hY : ∀k∈F,0<Y k) (Z : ℝ) (hZ : 0<Z)
    (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0<q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*markedPhysicalProbe η C (D k) W0 W1
      (X k) (Y k) (Z*∏i,q k i))=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*
        (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
          correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
            (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j))*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  obtain ⟨R,hR⟩ := physicalRows_common_finset C W0 W1 hW0 hW1 F X Y hX hY
  have hs (k : α) (hk : k∈F) (f : PhysicalRowIndex→ℂ) :
      (∑'r,physicalRowWeight C W0 W1 (X k) (Y k) r*f r)=
      ∑r∈R,physicalRowWeight C W0 W1 (X k) (Y k) r*f r :=
    tsum_eq_sum (fun r hr=>by rw [hR k hk r hr,zero_mul])
  let A (p : α×PhysicalRowIndex) := a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2
  have hh := gaussian_selected_tuple_reassembly W V hV hsep (F×ˢR) A C.excluded
    (fun p=>D p.1) (fun p=>physicalRowMonoid η C p.2)
    (fun p _=>physicalRowMonoid_norm η C p.2) Z hZ (fun p=>q p.1)
    (fun p hp=>hq p.1 (Finset.mem_product.mp hp).1)
  calc
    _ = ∑p∈F×ˢR,A p*(∏i,W i (q p.1 i))*correctedCompletedT C.excluded (D p.1)
      (physicalRowMonoid η C p.2) gaussianCompletedProfile (Z*∏i,q p.1 i) := by
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro k hk
        rw [markedPhysicalProbe_eq_gaussian_rows η C (D k) W0 W1 hW0 hW1
          (X k) (Y k) _ (hX k hk) (hY k hk) (mul_pos hZ (Finset.prod_pos (fun i _=>hq k hk i))),hs k hk]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        dsimp [A]
        ring
    _ = _ := hh
    _ = _ := by
      apply tsum_congr
      intro j
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      congr 1
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hs k hk,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      dsimp [A]
      ring

theorem physical_selected_gaussian_family {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀J : ℕ,∀s : ℝ,0<s→∃B : ℝ,0<B ∧ ∀Z : ℝ,0<Z→
        Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)) ∧
        (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z))≤B*Z^s) ∧
      (∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
        HasCompactSupport W0→HasCompactSupport W1→
        ∀F : Finset α,∀a : α→ℂ,∀D : α→Id,∀X Y : α→ℝ,
        (∀k∈F,0<X k)→(∀k∈F,0<Y k)→∀Z : ℝ,0<Z→
        ∀q : α→ι→ℝ,(∀k∈F,∀i,0<q k i)→
        (∑k∈F,a k*(∏i,W i (q k i))*markedPhysicalProbe η C (D k) W0 W1
          (X k) (Y k) (Z*∏i,q k i))=
          ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*
            (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
              correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
                (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j))*
            (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
              gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
  obtain ⟨V,hV,hsep,_⟩ := gaussian_selected_slot_family W M hM hwindow
  refine ⟨V,hV,fun J s hs=>gaussianJointMoment_summed V hV J s hs,?_⟩
  intro η C W0 W1 hW0 hW1 F a D X Y hX hY Z hZ q hq
  exact physical_selected_gaussian_reassembly W V hV hsep η C W0 W1 hW0 hW1
    F a D X Y hX hY Z hZ q hq

end SevenEighths.ProbePhysical
end

end OAI

end Source1375

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianCompensation.lean; sha256: 72d7f4fe4219cb5ee7aa82b97b468d6605cd7c40ebb2479fb38d37c9e909456d -/
section Source1376
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalElementNorm_pos (a : O) (ha : a≠0) : 0<elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))

lemma elementNorm_slotProduct {K : ℕ} (p : Fin K→O) (J : Finset (Fin K)) :
    elementNorm (slotProduct p J)=∏i∈J,elementNorm (p i) := by
  induction J using Finset.induction_on with
  | empty => simp [slotProduct,elementNorm_one]
  | @insert i J hi ih => simpa only [slotProduct,Finset.prod_insert hi,elementNorm_mul] using congrArg (fun x=>elementNorm (p i)*x) ih

lemma slotProduct_nonzero {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    slotProduct p J≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)

lemma slotProduct_norm_pos {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    0<elementNorm (slotProduct p J) := physicalElementNorm_pos _ (slotProduct_nonzero p hp J)

def compensationSubsetCoefficient {K : ℕ} (η : HeckeFamily.Character)
    (p : Fin K→O) (J : Finset (Fin K)) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (slotProduct p J)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (HeckeFamily.elementCoeff η (slotProduct p (Finset.univ\J)))

def compensationSubsetProbe {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (J : Finset (Fin K)) (X Y Z : ℝ) : ℂ :=
  compensationSubsetCoefficient η p J*
    markedPhysicalProbe η C (Ideal.span {slotProduct p (Finset.univ\J)}) W0 W1
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (Z*elementNorm (slotProduct p (Finset.univ\J)))

lemma compensatedTuple_eq_subsets {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (X Y Z : ℝ) :
    compensatedTuple η C W0 W1 p X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,compensationSubsetProbe η C W0 W1 p J X Y Z := rfl

lemma compensatedPhysicalProbe_eq_subsets {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slotPrimes : Fin K→Finset O)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (X Y Z : ℝ) :
    compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,
        ∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
          (∏i,W i (elementNorm (p i).val/P i))*
            compensationSubsetProbe η C W0 W1 (fun i=>(p i).val) J X Y Z := by
  unfold compensatedPhysicalProbe
  simp_rw [compensatedTuple_eq_subsets,Finset.mul_sum]
  exact Finset.sum_comm

theorem compensationSubsetProbe_eq_gaussian_rows {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensationSubsetProbe η C W0 W1 p J X Y Z=
      compensationSubsetCoefficient η p J*
        ∑'r : PhysicalRowIndex,
          physicalRowWeight C W0 W1 (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J)) r*
            correctedCompletedT C.excluded (Ideal.span {slotProduct p (Finset.univ\J)})
              (physicalRowMonoid η C r) gaussianCompletedProfile
                (Z*elementNorm (slotProduct p (Finset.univ\J))) := by
  unfold compensationSubsetProbe
  rw [markedPhysicalProbe_eq_gaussian_rows η C _ W0 W1 hW0 hW1 _ _ _
    (div_pos hX (slotProduct_norm_pos p hp J)) (div_pos hY (slotProduct_norm_pos p hp J))
    (mul_pos hZ (slotProduct_norm_pos p hp _))]

end SevenEighths.ProbePhysical
end

end OAI

end Source1376

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianSubset.lean; sha256: d3c66c1fe25820ac61ff34641cf84a5384851709462d1ad1a55b0237ed0f5a3a -/
section Source1377
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev SelectedSlot {K : ℕ} (J : Finset (Fin K)) := ↥(Finset.univ\J)

def compensationSubsetWeight {K : ℕ} (η : HeckeFamily.Character)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (p : Fin K→O) (J : Finset (Fin K)) : ℂ :=
  compensationSubsetCoefficient η p J*(∏i∈J,W i (elementNorm (p i)/P i))

def selectedSlotFactor {K : ℕ} (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (p : Fin K→O) (J : Finset (Fin K)) (t : ℝ) : ℂ :=
  ∏i : SelectedSlot J,W i.val (elementNorm (p i.val)/P i.val)*
    logPhase (-t) (Real.log (elementNorm (p i.val)/P i.val))

def compensationRowTest {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (J : Finset (Fin K)) (X Y T t : ℝ) : ℂ :=
  ∑'r : PhysicalRowIndex,
    physicalRowWeight C W0 W1 (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J)) r*
      correctedCompletedT C.excluded (Ideal.span {slotProduct p (Finset.univ\J)})
        (physicalRowMonoid η C r) (CompletedHeight.normTwistedSource gaussianFixedWindow t) T

lemma gaussian_slot_window_split {K : ℕ} (W : Fin K→ℝ→ℂ) (q : Fin K→ℝ) (J : Finset (Fin K)) :
    (∏i,W i (q i))=(∏i∈J,W i (q i))*(∏i : SelectedSlot J,W i.val (q i.val)) := by
  rw [Finset.prod_coe_sort (Finset.univ\J) (fun i=>W i (q i))]
  have hh := Finset.prod_sdiff (Finset.subset_univ J) (f:=fun i=>W i (q i))
  simpa only [mul_comm] using hh.symm

lemma gaussian_compensation_scale {K : ℕ} (P : Fin K→ℝ) (hP : ∀i,0<P i)
    (p : Fin K→O) (J : Finset (Fin K)) (Z : ℝ) :
    (Z*∏i∈Finset.univ\J,P i)*(∏i : SelectedSlot J,elementNorm (p i.val)/P i.val)=
      Z*elementNorm (slotProduct p (Finset.univ\J)) := by
  rw [←Finset.prod_coe_sort (Finset.univ\J) P]
  rw [gaussian_selected_scale Z (fun i : SelectedSlot J=>P i.val)
    (fun i : SelectedSlot J=>elementNorm (p i.val)) (fun i=>hP i.val)]
  rw [Finset.prod_coe_sort (Finset.univ\J) (fun i=>elementNorm (p i)),elementNorm_slotProduct]

theorem compensation_subset_common {K : ℕ} {α : Type*}
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : SelectedSlot J→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i.val (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i.val (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (p : α→Fin K→O) (hp : ∀k∈F,∀i,p k i≠0)
    (P : Fin K→ℝ) (hP : ∀i,0<P i) (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∑k∈F,(∏i,W i (elementNorm (p k i)/P i))*compensationSubsetProbe η C W0 W1 (p k) J X Y Z)=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,compensationSubsetWeight η W P (p k) J*
        compensationRowTest η C W0 W1 (p k) J X Y ((2:ℝ)^j) t*
          selectedSlotFactor W P (p k) J t)*
            gaussianJointDensity V hV ((2:ℝ)^j/(Z*∏i∈Finset.univ\J,P i)) t := by
  have hbase : 0<Z*∏i∈Finset.univ\J,P i := mul_pos hZ (Finset.prod_pos (fun i _=>hP i))
  have hh := physical_selected_gaussian_reassembly
    (fun i : SelectedSlot J=>W i.val) V hV hsep η C W0 W1 hW0 hW1 F
    (fun k=>compensationSubsetWeight η W P (p k) J)
    (fun k=>Ideal.span {slotProduct (p k) (Finset.univ\J)})
    (fun k=>X/elementNorm (slotProduct (p k) J)) (fun k=>Y/elementNorm (slotProduct (p k) J))
    (fun k hk=>div_pos hX (slotProduct_norm_pos (p k) (hp k hk) J))
    (fun k hk=>div_pos hY (slotProduct_norm_pos (p k) (hp k hk) J))
    (Z*∏i∈Finset.univ\J,P i) hbase
    (fun k (i : SelectedSlot J)=>elementNorm (p k i.val)/P i.val)
    (fun k hk i=>div_pos (physicalElementNorm_pos _ (hp k hk i.val)) (hP i.val))
  calc
    _ = ∑k∈F,compensationSubsetWeight η W P (p k) J*
      (∏i : SelectedSlot J,W i.val (elementNorm (p k i.val)/P i.val))*
        markedPhysicalProbe η C (Ideal.span {slotProduct (p k) (Finset.univ\J)}) W0 W1
          (X/elementNorm (slotProduct (p k) J)) (Y/elementNorm (slotProduct (p k) J))
          ((Z*∏i∈Finset.univ\J,P i)*(∏i : SelectedSlot J,elementNorm (p k i.val)/P i.val)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [gaussian_compensation_scale P hP (p k) J Z,gaussian_slot_window_split W (fun i=>elementNorm (p k i)/P i) J]
      unfold compensationSubsetProbe compensationSubsetWeight
      ring
    _ = _ := hh

end SevenEighths.ProbePhysical
end

end OAI

end Source1377

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowCompensation.lean; sha256: 72434463a783cf5d62f4d1014cb3df31431ce0a87522cc6c887caf78fc084c8a -/
section Source1378
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted CanonicalRowCompletion RayFourExpansion ProbeRow CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowMarkedInverseRow (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (D : Id) (T t : ℝ) (σ : RayRing) (m : O) : ℂ :=
  ∑χ : RayCharacter,correctionCoeff χ*
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator 1 m)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
      (fun A=>if D∣A then (1:ℂ) else 0)

lemma lowMarkedInverseRow_eq (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (D : Id) (T t : ℝ) (hT : 0<T)
    (σ : RayRing) (m : O) :
    correctedCompletedT S D (physicalRayRowMonoid η (calibrationForSet S hS) σ m)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T=
        lowMarkedInverseRow η S hS D T t σ m :=
  physicalRayRow_eq_periodic_inverse η S hS hbad σ m D _ (gaussianFixedWindow_twist_compact t) T hT

theorem compensationRowTest_low_separated {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    compensationRowTest η (calibrationForSet S hS) W0 W1 p J X Y T t=
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
          (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t) v := by
  unfold compensationRowTest
  simp_rw [physicalRowMonoid_eq_ray]
  have hC : (calibrationForSet S hS).excluded=S := calibrationForSet_excluded S hS
  rw [hC]
  simp_rw [lowMarkedInverseRow_eq η S hS hbad _ T t hT]
  exact physicalRowWeight_low_separated (calibrationForSet S hS) W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hWs _ _ (div_pos hX (slotProduct_norm_pos p hp J))
      (div_pos hY (slotProduct_norm_pos p hp J))
      (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t)

lemma compensationRowTest_low_integrable {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) :
    Integrable (lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
      (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t)) := by
  exact lowSeparatedIntegrand_integrable (calibrationForSet S hS) W0 W1 _ a0 b0 ha0 hW0 hWs
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    (lowOuterCutoff_compact _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
    (lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)) _ _
    (div_pos hX (slotProduct_norm_pos p hp J)) (div_pos hY (slotProduct_norm_pos p hp J)) _

end SevenEighths.ProbePhysical
end

end OAI

end Source1378

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowSelectedSum.lean; sha256: 8992273342b3dc16026d48068d2f7e0f148a5214e0327b9f9d36405aa33e543e -/
section Source1379
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowSeparatedIntegrand_finite_sum {α : Type*} (F : Finset α) (c : α→ℂ)
    (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ) (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : α→RayRing→O→ℂ) (v : ℝ) :
    (∑k∈F,c k*lowSeparatedIntegrand C W0 W1 Ω X Y (B k) v)=
      lowSeparatedIntegrand C W0 W1 Ω X Y (fun σ m=>∑k∈F,c k*B k σ m) v := by
  simp_rw [←lowSeparatedIntegrand_eq C W0 W1 Ω hW1 hΩ X Y hX hY]
  simp_rw [←tsum_mul_left]
  rw [←Summable.tsum_finsetSum (fun k _=>
    (lowRowMellinIntegrand_mul_summable C W0 W1 Ω hW1 hΩ X Y hX hY v
      (fun r=>B k (physicalIdealRay r.1) r.2)).mul_left (c k))]
  apply tsum_congr
  intro r
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma lowSeparatedIntegral_finite_sum {α : Type*} (F : Finset α) (c : α→ℂ)
    (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : α→RayRing→O→ℂ) :
    (∑k∈F,c k*∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω X Y (B k) v)=
      ∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω X Y (fun σ m=>∑k∈F,c k*B k σ m) v := by
  simp_rw [←integral_const_mul]
  rw [←integral_finsetSum F (fun k _=>(lowSeparatedIntegrand_integrable C W0 W1 Ω
    a0 b0 ha0 hW0 hWs hW1 hΩ hΩ0 X Y hX hY (B k)).const_mul (c k))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v=>lowSeparatedIntegrand_finite_sum F c C W0 W1 Ω hW1 hΩ X Y hX hY B v)

def lowSelectedInverseRow {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (m : O) : ℂ :=
  ∑k∈F,c k*lowMarkedInverseRow η S hS (D k) T t σ m

lemma lowSelectedInverseRow_correction {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (m : O) :
    lowSelectedInverseRow F c η S hS D T t σ m=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        ∑k∈F,c k*InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
          (fun A=>if D k∣A then (1:ℂ) else 0) := by
  unfold lowSelectedInverseRow lowMarkedInverseRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro k hk
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1379

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowSlotSplit.lean; sha256: 6d38232a49b27e4de08952f55405cafbf331921e753c200f1735464d38e7566f -/
section Source1380
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

abbrev LowUnselectedTuple {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :=
  ∀i : J,↥(slots i.val)
abbrev LowSelectedTuple {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :=
  ∀i : SelectedSlot J,↥(slots i.val)

def lowSlotTupleEquiv {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :
    (∀i,↥(slots i)) ≃ LowUnselectedTuple slots J×LowSelectedTuple slots J where
  toFun p := (fun i=>p i.val,fun i=>p i.val)
  invFun p i := if hi : i∈J then p.1 ⟨i,hi⟩ else p.2 ⟨i,by simp [hi]⟩
  left_inv p := by
    funext i
    dsimp only
    split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      simp only [dite_eq_left i.property]
    · funext i
      have hi : i.val∉J := (Finset.mem_sdiff.mp i.property).2
      simp only [dite_eq_right hi]

def lowSlotJoin {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) : Fin K→O :=
  fun i=>((lowSlotTupleEquiv slots J).symm (a,b) i).val

lemma lowSlotJoin_nonzero {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : Fin K) :
    lowSlotJoin slots J a b i≠0 := hslots i _ ((lowSlotTupleEquiv slots J).symm (a,b) i).property

lemma lowSlotJoin_unselected {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : J) :
    lowSlotJoin slots J a b i.val=(a i).val := by
  simp only [lowSlotJoin,lowSlotTupleEquiv,Equiv.coe_fn_symm_mk,dite_eq_left i.property]

lemma lowSlotJoin_selected {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : SelectedSlot J) :
    lowSlotJoin slots J a b i.val=(b i).val := by
  have hi : i.val∉J := (Finset.mem_sdiff.mp i.property).2
  simp only [lowSlotJoin,lowSlotTupleEquiv,Equiv.coe_fn_symm_mk,dite_eq_right hi]

lemma lowSlotJoin_unselectedProduct {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    slotProduct (lowSlotJoin slots J a b) J=∏i : J,(a i).val := by
  unfold slotProduct
  rw [←Finset.prod_coe_sort J]
  simp only [lowSlotJoin_unselected]

lemma lowSlotJoin_selectedProduct {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    slotProduct (lowSlotJoin slots J a b) (Finset.univ\J)=∏i : SelectedSlot J,(b i).val := by
  unfold slotProduct
  rw [←Finset.prod_coe_sort (Finset.univ\J)]
  simp only [lowSlotJoin_selected]

lemma lowSlotJoin_selectedFactor {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ) :
    selectedSlotFactor W P (lowSlotJoin slots J a b) J t=
      ∏i : SelectedSlot J,W i.val (elementNorm (b i).val/P i.val)*
        FourierBridge.logPhase (-t) (Real.log (elementNorm (b i).val/P i.val)) := by
  unfold selectedSlotFactor
  simp only [lowSlotJoin_selected]

theorem sum_lowSlotJoin {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(slots i)),F (fun i=>(p i).val))=
      ∑a : LowUnselectedTuple slots J,∑b : LowSelectedTuple slots J,F (lowSlotJoin slots J a b) := by
  calc
    _ = ∑p : LowUnselectedTuple slots J×LowSelectedTuple slots J,F (lowSlotJoin slots J p.1 p.2) :=
      (Equiv.sum_comp (lowSlotTupleEquiv slots J).symm (fun p=>F (fun i=>(p i).val))).symm
    _ = _ := Fintype.sum_prod_type _

end SevenEighths.ProbePhysical
end

end OAI

end Source1380

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowSlotPolynomial.lean; sha256: 9ae3f903bfe58745d2bd4664b34fafd1dd4bb92eb32993dcc9d89b2ce120246e -/
section Source1381
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowUnselectedWeight {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (a : LowUnselectedTuple slots J) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (∏i : J,(a i).val)^(-(3/2:ℝ)):ℝ):ℂ)*
    ∏i : J,W i.val (elementNorm (a i).val/P i.val)

def lowSelectedWeight {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) : ℂ :=
  star (HeckeFamily.elementCoeff η (∏i : SelectedSlot J,(b i).val))*
    ∏i : SelectedSlot J,W i.val (elementNorm (b i).val/P i.val)*
      FourierBridge.logPhase (-t) (Real.log (elementNorm (b i).val/P i.val))

def lowSelectedIdeal {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J) : Id := Ideal.span {∏i : SelectedSlot J,(b i).val}

lemma lowSlotJoin_weight {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    compensationSubsetWeight η W P (lowSlotJoin slots J a b) J*
      selectedSlotFactor W P (lowSlotJoin slots J a b) J t=
        lowUnselectedWeight slots J W P a*lowSelectedWeight η slots J W P t b := by
  unfold compensationSubsetWeight compensationSubsetCoefficient
  rw [lowSlotJoin_unselectedProduct,lowSlotJoin_selectedProduct,lowSlotJoin_selectedFactor]
  rw [←Finset.prod_coe_sort J (fun i=>W i (elementNorm (lowSlotJoin slots J a b i)/P i))]
  simp only [lowSlotJoin_unselected]
  unfold lowUnselectedWeight lowSelectedWeight
  ring

lemma lowUnselectedProduct_norm_pos {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    0<elementNorm (∏i : J,(a i).val) := by
  apply physicalElementNorm_pos
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>hslots i.val _ (a i).property)

lemma compensationRowTest_join_low {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (slots : Fin K→Finset O) (hslots : ∀i x,x∈slots i→x≠0)
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J)
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    compensationRowTest η (calibrationForSet S hS) W0 W1 (lowSlotJoin slots J a b) J X Y T t=
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v := by
  simpa only [lowSlotJoin_unselectedProduct,lowSlotJoin_selectedProduct,lowSelectedIdeal] using
    compensationRowTest_low_separated η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs
      (lowSlotJoin slots J a b) (lowSlotJoin_nonzero slots hslots J a b) J X Y T t hX hY hT

theorem compensation_tuple_low_polynomial {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (slots : Fin K→Finset O) (hslots : ∀i x,x∈slots i→x≠0)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    (∑p : (∀i,↥(slots i)),compensationSubsetWeight η W P (fun i=>(p i).val) J*
      compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J X Y T t*
        selectedSlotFactor W P (fun i=>(p i).val) J t)=
      ∑a : LowUnselectedTuple slots J,lowUnselectedWeight slots J W P a*
        ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ))*
          ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
            (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
            (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
            (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W P t)
              η S hS (lowSelectedIdeal slots J) T t) v := by
  rw [sum_lowSlotJoin slots J (fun p=>compensationSubsetWeight η W P p J*
    compensationRowTest η (calibrationForSet S hS) W0 W1 p J X Y T t*selectedSlotFactor W P p J t)]
  apply Finset.sum_congr rfl
  intro a ha
  let L := elementNorm (∏i : J,(a i).val)
  have hL : 0<L := lowUnselectedProduct_norm_pos slots hslots J a
  let C := calibrationForSet S hS
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  let N : ℂ := (Real.sqrt (lowPhysicalScale C (X/L) (Y/L)):ℂ)⁻¹*(1/(2*Real.pi):ℂ)
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  have hΩc : HasCompactSupport Ω := lowOuterCutoff_compact _ _ (mul_pos ha0 ha1)
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hΩ0 : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  calc
    _ = lowUnselectedWeight slots J W P a*N*
        ∑b : LowSelectedTuple slots J,lowSelectedWeight η slots J W P t b*
          ∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω (X/L) (Y/L)
            (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [compensationRowTest_join_low η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs
        slots hslots J a b X Y T t hX hY hT]
      have hw := lowSlotJoin_weight η slots J W P t a b
      dsimp only [C,Ω,L,N]
      linear_combination (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*
        (1/(2*Real.pi):ℂ)*(∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v)*hw
    _ = _ := by
      rw [lowSeparatedIntegral_finite_sum Finset.univ (lowSelectedWeight η slots J W P t)
        C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1c hΩc hΩ0 (X/L) (Y/L)
        (div_pos hX hL) (div_pos hY hL)]
      rfl

end SevenEighths.ProbePhysical
end

end OAI

end Source1381

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowSlotMarks.lean; sha256: 3c05f758d87bb2c077db063ba2919ac7ef88d1ef8cd33e256e62b23245d65f6e -/
section Source1382
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowSelectedIdeal_eq_product {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J) :
    lowSelectedIdeal slots J b=∏i : SelectedSlot J,Ideal.span {(b i).val} := by
  change CanonicalRowCompletion.principalIdealHom (∏i : SelectedSlot J,(b i).val)=_
  exact map_prod CanonicalRowCompletion.principalIdealHom _ _

lemma lowSelectedIdeal_dvd_iff {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J)
    (hcop : Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})))
    (A : Id) : lowSelectedIdeal slots J b∣A ↔ ∀i : SelectedSlot J,Ideal.span {(b i).val}∣A := by
  rw [lowSelectedIdeal_eq_product]
  constructor
  · intro h i
    exact (Finset.dvd_prod_of_mem (fun i : SelectedSlot J=>Ideal.span {(b i).val}) (Finset.mem_univ i)).trans h
  · exact Fintype.prod_dvd_of_coprime hcop

lemma lowSelectedIdeal_mark {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J)
    (hcop : Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})))
    (A : Id) :
    (if lowSelectedIdeal slots J b∣A then (1:ℂ) else 0)=
      ∏i : SelectedSlot J,if Ideal.span {(b i).val}∣A then (1:ℂ) else 0 := by
  rw [lowSelectedIdeal_dvd_iff slots J b hcop]
  by_cases h : ∀i : SelectedSlot J,Ideal.span {(b i).val}∣A
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [ite_eq_right (fun hall=>hi (hall i))]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

def lowCanonicalSelectedPrime {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) : PrimeIdeal :=
  ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i)).val

lemma lowCanonicalSelectedPrime_mem {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    lowCanonicalSelectedPrime T hT J b i∈T i.val :=
  ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i)).property

lemma lowCanonicalSelectedPrime_span {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    Ideal.span {(b i).val}=(lowCanonicalSelectedPrime T hT J b i).val := by
  have hh := canonicalSlotEquiv_span (T i.val) (hT i.val)
    ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i))
  simpa only [Equiv.apply_symm_apply,lowCanonicalSelectedPrime] using hh

lemma lowCanonicalSelectedPrime_injective {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Function.Injective (lowCanonicalSelectedPrime T hT J b) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  exact Finset.disjoint_left.mp (hdis hne) (lowCanonicalSelectedPrime_mem T hT J b i)
    (hij.symm ▸ lowCanonicalSelectedPrime_mem T hT J b j)

lemma lowCanonicalSelected_coprime {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})) := by
  intro i j hij
  rw [lowCanonicalSelectedPrime_span T hT J b i,lowCanonicalSelectedPrime_span T hT J b j]
  exact primeIdeal_coprime _ _ (fun h=>hij (lowCanonicalSelectedPrime_injective T hT hdis J b h))

theorem lowCanonicalSelected_mark {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (A : Id) :
    (if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
      ∏i : SelectedSlot J,if (lowCanonicalSelectedPrime T hT J b i).val∣A then (1:ℂ) else 0 := by
  rw [lowSelectedIdeal_mark _ J b (lowCanonicalSelected_coprime T hT hdis J b)]
  simp_rw [lowCanonicalSelectedPrime_span T hT J b]

end SevenEighths.ProbePhysical
end

end OAI

end Source1382

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowSlotWeights.lean; sha256: ea0501da5e20d644336933979785e1adb5ae43591bc10287d08c720b81ee17d3 -/
section Source1383
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow FourierBridge
local notation "O" => ActualEisensteinCubic.O

def lowSingleSlotWeight (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) : ℂ :=
  star (HeckeFamily.elementCoeff η a)*W (elementNorm a/P)*logPhase (-t) (Real.log (elementNorm a/P))

lemma lowSelectedWeight_eq_product {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    lowSelectedWeight η slots J W P t b=
      ∏i : SelectedSlot J,lowSingleSlotWeight η (W i.val) (P i.val) t (b i).val := by
  have he : HeckeFamily.elementCoeff η (∏i : SelectedSlot J,(b i).val)=
      ∏i : SelectedSlot J,HeckeFamily.elementCoeff η (b i).val := map_prod (targetMonoid η) _ _
  unfold lowSelectedWeight lowSingleSlotWeight
  rw [he,star_prod]
  simp only [Finset.prod_mul_distrib,mul_assoc]

lemma lowSingleSlotWeight_norm (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) :
    ‖lowSingleSlotWeight η W P t a‖≤‖W (elementNorm a/P)‖ := by
  rw [lowSingleSlotWeight,norm_mul,norm_mul,norm_star,logPhase_norm,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)

lemma lowSingleSlotWeight_height_norm (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) :
    ‖lowSingleSlotWeight η W P t a‖=‖lowSingleSlotWeight η W P 0 a‖ := by
  simp only [lowSingleSlotWeight,norm_mul,logPhase_norm,mul_one]

lemma lowSelectedWeight_norm {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖≤∏i : SelectedSlot J,‖W i.val (elementNorm (b i).val/P i.val)‖ := by
  rw [lowSelectedWeight_eq_product,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun i _=>lowSingleSlotWeight_norm η (W i.val) (P i.val) t (b i).val)

lemma lowSelectedWeight_height_norm {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖=‖lowSelectedWeight η slots J W P 0 b‖ := by
  rw [lowSelectedWeight_eq_product,lowSelectedWeight_eq_product,norm_prod,norm_prod]
  exact Finset.prod_congr rfl (fun i _=>lowSingleSlotWeight_height_norm η (W i.val) (P i.val) t (b i).val)

lemma lowSelectedWeight_norm_le_one {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (hW : ∀i x,‖W i x‖≤1) (t : ℝ) (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖≤1 :=
  (lowSelectedWeight_norm η slots J W P t b).trans
    (Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i _=>hW i.val _))

end SevenEighths.ProbePhysical
end

end OAI

end Source1383

/- Original source: OAI/NumberTheory/DirichletL/Descent/LocalReflection.lean; sha256: 119edaab53aa2758c20702d14fef80aebe43c68072589e430d931dc1f9ca5afc -/
section Source1384
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators Classical

noncomputable section

variable {F : Type*} [Field F] [Fintype F]

def zeroMark (x : F) : ℂ := if x = 0 then 1 else 0

def localFourier (f : F → ℂ) (ψ : AddChar F ℂ) (h : F) : ℂ :=
  ∑ t : F, f t * ψ (-(h * t))

theorem localFourier_zeroMark (ψ : AddChar F ℂ) (h : F) :
    localFourier zeroMark ψ h = 1 := by
  simp [localFourier, zeroMark]

theorem localFourier_trivial_nonzero (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (h : F) (hh : h ≠ 0) :
    localFourier (fun t => (1 : MulChar F ℂ) t) ψ h = -1 := by
  have he := gaussSum_one_left (hψ (neg_ne_zero.mpr hh))
  simpa only [gaussSum, AddChar.mulShift_apply, neg_mul, localFourier] using he

omit [Fintype F] in
theorem zeroMark_complement (x : F) :
    zeroMark x = 1 - (1 : MulChar F ℂ) x := by
  by_cases hx : x = 0
  · simp [zeroMark, hx, MulChar.map_zero]
  · rw [zeroMark, ite_eq_right hx, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
    ring

def localReflectionActive (f : F → ℂ) (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (σ ε : Fˣ) (x : F) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ * ∑ h : Fˣ,
    localFourier f ψ h * ((χ⁻¹) ^ 2) (σ * h) *
      ψ (((ε : F) * x) * ((h⁻¹ : Fˣ) : F))

theorem marked_active_eq_neg_trivial (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (σ ε : Fˣ) (x : F) :
    localReflectionActive zeroMark χ ψ σ ε x =
      -localReflectionActive (fun t => (1 : MulChar F ℂ) t) χ ψ σ ε x := by
  unfold localReflectionActive
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [localFourier_zeroMark, localFourier_trivial_nonzero ψ hψ h (Units.ne_zero h)]
  ring

theorem marked_inactive_coefficient (ψ : AddChar F ℂ) :
    (Fintype.card F : ℂ)⁻¹ * localFourier zeroMark ψ 0 =
      (Fintype.card F : ℂ)⁻¹ := by
  rw [localFourier_zeroMark, mul_one]

end

end SevenEighths.InverseMoment

end OAI

end Source1384

/- Original source: OAI/NumberTheory/DirichletL/Descent/Poisson.lean; sha256: 9eb0091bed56c7982a4d95e4526b05fe20280287750ec0b6992cb8405c8293df -/
section Source1385
namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open FirstPassCubeLabels
open SecondPassArithmetic

noncomputable local instance markedQuotientField (P : Ideal ActualEisensteinCubic.O)
    [P.IsMaximal] : Field (ActualEisensteinCubic.O ⧸ P) := Ideal.Quotient.field P

noncomputable local instance markedQuotientFintype (P : Ideal ActualEisensteinCubic.O)
    [P.IsMaximal] : Fintype (ActualEisensteinCubic.O ⧸ P) := Fintype.ofFinite _

theorem ideal_divisibility_local_zeroMark
    (P A : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hA : CompletedGauss.primaryGenerator A ≠ 0) :
    zeroMark (Ideal.Quotient.mk P (CompletedGauss.primaryGenerator A)) =
      if P ∣ A then 1 else 0 := by
  have hd : P ∣ A ↔ CompletedGauss.primaryGenerator A ∈ P := by
    calc
      P ∣ A ↔ A ≤ P := Ideal.dvd_iff_le
      _ ↔ Ideal.span {CompletedGauss.primaryGenerator A} ≤ P := by
        rw [(CompletedGauss.primaryGenerator_spec A hA).1]
      _ ↔ _ := Ideal.span_singleton_le_iff_mem P
  simp only [zeroMark, Ideal.Quotient.eq_zero_iff_mem, hd]

theorem actual_marked_active_eq
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    localReflectionActive zeroMark (CompletedGauss.actualSextic P hg) ψ σ ε x =
      -LocalReflectionBrackets.activeRow (CompletedGauss.actualSextic P hg) ψ 0 σ ε x := by
  simpa only [localReflectionActive, localFourier,
    LocalReflectionBrackets.activeRow, pow_zero] using
    marked_active_eq_neg_trivial (CompletedGauss.actualSextic P hg) ψ hψ σ ε x

theorem actual_marked_active_norm
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hchar : ringChar (ActualEisensteinCubic.O ⧸ P) ≠ 2)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    ‖localReflectionActive zeroMark (CompletedGauss.actualSextic P hg) ψ σ ε x‖ =
      (LocalReflectionBrackets.rootCard (ActualEisensteinCubic.O ⧸ P))⁻¹ *
        if x = 0 then 0 else 1 := by
  rw [actual_marked_active_eq P hg ψ hψ σ ε x, norm_neg,
    LocalReflectionBrackets.canonical_A5_norm_eq_bracket P hg hchar ψ hψ 0
      (by norm_num) σ ε x, LocalReflectionBrackets.norm_bracket_zero]

theorem actual_marked_active_formula
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hchar : ringChar (ActualEisensteinCubic.O ⧸ P) ≠ 2)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    localReflectionActive zeroMark (CompletedGauss.actualSextic P hg) ψ σ ε x =
      (LocalReflectionBrackets.rootCard (ActualEisensteinCubic.O ⧸ P) : ℂ)⁻¹ *
        LocalReflectionBrackets.tau (CompletedGauss.actualSextic P hg) ψ 2 *
        (((CompletedGauss.actualSextic P hg) ^ 2)⁻¹)
          ((σ : ActualEisensteinCubic.O ⧸ P) * (ε : ActualEisensteinCubic.O ⧸ P) * x) := by
  rw [actual_marked_active_eq P hg ψ hψ σ ε x,
    LocalReflectionBrackets.canonical_A5_normalized P hg hchar ψ hψ 0 (by norm_num)]
  simp only [LocalReflectionBrackets.phase, LocalReflectionBrackets.bracket,
    show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, inv_pow, map_mul]
  ring

theorem actual_marked_gauss_phase_norm
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hchar : ringChar (ActualEisensteinCubic.O ⧸ P) ≠ 2)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    ‖LocalReflectionBrackets.tau (CompletedGauss.actualSextic P hg) ψ 2‖ = 1 := by
  have h := LocalReflectionBrackets.canonical_phase_norm P hg hchar ψ hψ 0 (by norm_num) 1
  simpa only [LocalReflectionBrackets.phase, show (0 : ℕ) ≠ 4 by decide,
    ↓reduceIte, Units.val_one, map_one, mul_one, norm_neg] using h

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hcop

omit [DecidableEq ι] in
theorem row_slot_cross_phase
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k) :
    MixedCrossSeparation.crossSymbol p hg i k ^ 4 *
      MixedCrossSeparation.crossSymbol p hg k i ^ 2 = 1 := by
  have hs : MixedCrossSeparation.crossSymbol p hg i k ^ 2 =
      MixedCrossSeparation.crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  have h6 : MixedCrossSeparation.crossSymbol p hg i k ^ 6 = 1 := by
    simpa only [MixedCrossSeparation.crossSymbol, map_pow, ite_eq_right hnot] using
      canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)
  calc
    _ = MixedCrossSeparation.crossSymbol p hg i k ^ 6 := by rw [← hs]; ring
    _ = 1 := h6

omit [DecidableEq ι] in
theorem row_slot_product_phase
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1) (R P : Finset ι) (hRP : Disjoint R P) :
    (∏ i ∈ R, ∏ k ∈ P,
      MixedCrossSeparation.crossSymbol p hg i k ^ 4 *
        MixedCrossSeparation.crossSymbol p hg k i ^ 2) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  apply Finset.prod_eq_one
  intro k hk
  exact row_slot_cross_phase p hcop hg hpr i k (fun h =>
    (Finset.disjoint_left.mp hRP) hi (h.symm ▸ hk))

theorem canonicalSourceCoefficient_mark_priority
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A S : Finset ι) :
    canonicalSourceCoefficient p hp hcop hg Ψ m f
      (fun U => H U * primeMark I L a (A ∪ U)) S =
    ∑ J ∈ I.powerset, primeMark J L a A *
      canonicalSourceCoefficient p hp hcop hg Ψ m f
        (fun U => H U * primeMark (I \ J) L a (U \ A)) S := by
  simp only [canonicalSourceCoefficient, primeMark_priority, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

omit [DecidableEq σ] in
theorem marked_disjoint_source_poisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (F M B A₁ A₂ : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (C₁ C₂ : Finset ι → ℂ) (I₁ I₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ K : ℝ) (hK : 0 < K) :
    disjointCanonicalSource p hp hcop hg F M B v ε₁ ε₂
      (fun U => C₁ U * primeMark I₁ L₁ a₁ (A₁ ∪ U))
      (fun U => C₂ U * primeMark I₂ L₂ a₂ (A₂ ∪ U)) W V₁ V₂ X₁ X₂ K =
    ∑ D ∈ M.powerset,
      (UniqueFactorizationMonoid.moebius (∏ i ∈ D, Ideal.span {p i}) : ℂ) /
        (primeProductNorm p D : ℂ) *
      ∑' h : ActualEisensteinCubic.O,
        actualFirstKernel p hp hcop hg F B v ε₁ ε₂
          (fun U => C₁ U * primeMark I₁ L₁ a₁ (A₁ ∪ U))
          (fun U => C₂ U * primeMark I₂ L₂ a₂ (A₂ ∪ U)) W V₁ V₂ X₁ X₂ K
          (primeSubsetGenerator (fun i => Ideal.span {p i}) D) h := by
  exact disjointCanonicalSource_poisson p hp hcop hg hinj hc F M B v ε₁ ε₂
    (fun U => C₁ U * primeMark I₁ L₁ a₁ (A₁ ∪ U))
    (fun U => C₂ U * primeMark I₂ L₂ a₂ (A₂ ∪ U)) W V₁ V₂ X₁ X₂ K hK

end

end SevenEighths.InverseMoment

end OAI

end Source1385

/- Original source: OAI/NumberTheory/DirichletL/Descent/MarkedFourier.lean; sha256: 11bf17c4b3e796cafaff7ed7b25b8f7b07b4cb689504c34dee638eb33daae7b8 -/
section Source1386
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion
open CubicEisenstein hiding summand
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem completed_summand_primary_support (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (X : ℝ) (I J : Ideal Eis) (h : summand Ψ W X I J ≠ 0) :
    primaryGenerator (I * J ^ 3) ≠ 0 := by
  have hI : primaryGenerator I ≠ 0 := by
    intro hz
    apply h
    simp [summand, columnWeight, squarefreeGaussCoefficient, hz]
  have hJ : primaryGenerator J ≠ 0 := by
    intro hz
    apply h
    rw [summand, cubeWeight_zero_of_primaryGenerator_zero Ψ J hz]
    ring
  rw [primaryGenerator_mul, show primaryGenerator (J ^ 3) = primaryGenerator J ^ 3 from
    map_pow primaryGeneratorHom J 3]
  exact mul_ne_zero hI (pow_ne_zero _ hJ)

theorem markedCompletedT_congr_primary (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d e : Ideal Eis → ℂ) (h : ∀ A, primaryGenerator A ≠ 0 → d A = e A) :
    markedCompletedT Ψ W X d = markedCompletedT Ψ W X e := by
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hz : summand Ψ W X I J = 0
  · simp only [hz, zero_mul]
  · rw [h (I * J ^ 3) (completed_summand_primary_support Ψ W X I J hz)]

theorem markedCompletedT_quotient_fourier (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})] (F : (Eis ⧸ Ideal.span {c}) → ℂ)
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => F (Ideal.Quotient.mk _ (primaryGenerator A))) =
      ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc) F h *
        completedFixedFrequency Ψ c hc h W X := by
  have hinv (n : Eis) :
      F (Ideal.Quotient.mk _ n) =
        ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc) F h *
          fixedRowFourierPhase c hc h n :=
    (finiteAdditiveFourier_inversion (quotientTrace c hc)
      (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) F (Ideal.Quotient.mk _ n)).symm
  have hp (p : Ideal Eis × Ideal Eis) :
      summand Ψ W X p.1 p.2 * F (Ideal.Quotient.mk _ (primaryGenerator (p.1 * p.2 ^ 3))) =
      ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc) F h *
        (summand Ψ W X p.1 p.2 * fixedRowFourierPhase c hc h
          (primaryGenerator p.1 * primaryGenerator p.2 ^ 3)) := by
    rw [primaryGenerator_mul, show primaryGenerator (p.2 ^ 3) = primaryGenerator p.2 ^ 3 from
      map_pow primaryGeneratorHom p.2 3, hinv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [markedCompletedT_eq_tsum Ψ W hW X hX]
  simp_rw [hp]
  rw [Summable.tsum_finsetSum]
  · simp only [tsum_mul_left, completedFixedFrequency]
  · intro h hh
    exact (completedFixedFrequency_summable Ψ c hc h W hW X hX).mul_left _

theorem finiteAdditiveFourierCoeff_zero_delta {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (h : R) :
    finiteAdditiveFourierCoeff ψ (fun x => if x = 0 then 1 else 0) h =
      (Fintype.card R : ℂ)⁻¹ := by
  simp [finiteAdditiveFourierCoeff]

theorem markedCompletedT_divisor_fourier (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => if Ideal.span {c} ∣ A then 1 else 0) =
      (Fintype.card (Eis ⧸ Ideal.span {c}) : ℂ)⁻¹ *
        ∑ h : Eis ⧸ Ideal.span {c}, completedFixedFrequency Ψ c hc h W X := by
  have hmark : markedCompletedT Ψ W X (fun A => if Ideal.span {c} ∣ A then 1 else 0) =
      markedCompletedT Ψ W X (fun A =>
        if Ideal.Quotient.mk (Ideal.span {c}) (primaryGenerator A) = 0 then 1 else 0) := by
    apply markedCompletedT_congr_primary
    intro A hA
    have hd : Ideal.span {c} ∣ A ↔
        Ideal.Quotient.mk (Ideal.span {c}) (primaryGenerator A) = 0 := by
      calc
        _ ↔ A ≤ Ideal.span {c} := Ideal.dvd_iff_le
        _ ↔ Ideal.span {primaryGenerator A} ≤ Ideal.span {c} := by
          rw [(primaryGenerator_spec A hA).1]
        _ ↔ primaryGenerator A ∈ Ideal.span {c} := Ideal.span_singleton_le_iff_mem _
        _ ↔ _ := (Ideal.Quotient.eq_zero_iff_mem).symm
    simp only [hd]
  rw [hmark, markedCompletedT_quotient_fourier c hc
    (fun x : Eis ⧸ Ideal.span {c} => if x = 0 then (1 : ℂ) else 0) Ψ W hW X hX]
  simp only [finiteAdditiveFourierCoeff_zero_delta, Finset.mul_sum]

end
end SevenEighths.InverseMoment

end OAI

end Source1386

/- Original source: OAI/NumberTheory/DirichletL/Descent/MarkedTwists.lean; sha256: 410fdeaedac267e1394a550bbb40557de62dcd7d89ddf0756bfc56af63073a39 -/
section Source1387
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem markedCompletedT_monoid (Ψ φ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    markedCompletedT Ψ W X (fun A => φ (primaryGenerator A)) = completedT (φ * Ψ) W X := by
  unfold markedCompletedT completedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  change summand Ψ W X I J * φ (primaryGenerator (I * J ^ 3)) = _
  rw [summand_mul_fixed_twist, primaryGenerator_mul,
    show primaryGenerator (J ^ 3) = primaryGenerator J ^ 3 from map_pow primaryGeneratorHom J 3]
  exact mul_comm _ _

theorem whole_prime_mark_eq_mask_complement (p : Eis) (hp : Prime p)
    (A : Ideal Eis) (hA : primaryGenerator A ≠ 0) :
    (if Ideal.span {p} ∣ A then (1 : ℂ) else 0) =
      1 - coprimalityMask p (primaryGenerator A) := by
  have hd : Ideal.span {p} ∣ A ↔ p ∣ primaryGenerator A := by
    calc
      _ ↔ A ≤ Ideal.span {p} := Ideal.dvd_iff_le
      _ ↔ Ideal.span {primaryGenerator A} ≤ Ideal.span {p} := by
        rw [(primaryGenerator_spec A hA).1]
      _ ↔ _ := by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
  change (if Ideal.span {p} ∣ A then (1 : ℂ) else 0) =
    1 - (if IsCoprime p (primaryGenerator A) then 1 else 0)
  rw [hp.coprime_iff_not_dvd]
  by_cases h : p ∣ primaryGenerator A <;> simp [hd, h]

theorem markedCompletedT_prime_product_twists {ι : Type*}
    (S : Finset ι) (p : ι → Eis) (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
        completedT ((∏ i ∈ T, coprimalityMask (p i)) * Ψ) W X := by
  have he : markedCompletedT Ψ W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      markedCompletedT Ψ W X (fun A =>
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
          (∏ i ∈ T, coprimalityMask (p i)) (primaryGenerator A)) := by
    apply markedCompletedT_congr_primary
    intro A hA
    calc
      _ = ∏ i ∈ S, (1 - coprimalityMask (p i) (primaryGenerator A)) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact whole_prime_mark_eq_mask_complement (p i) (hp i hi) A hA
      _ = _ := by
        rw [Finset.prod_sub]
        simp
  rw [he, markedCompletedT_finset_sum S.powerset Ψ W hW X hX]
  apply Finset.sum_congr rfl
  intro T hT
  rw [markedCompletedT_const_mul, markedCompletedT_monoid]

end
end SevenEighths.InverseMoment

end OAI

end Source1387

/- Original source: OAI/NumberTheory/DirichletL/Descent/MarkedReflection.lean; sha256: 874b8c29b68a983447f868c820d728408d5de158df1b589cd8b033ad6dd54ee1 -/
section Source1388
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open CompletedGauss CanonicalRowCompletion CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*}

def markTwist (p : ι → Eis) (T : Finset ι) : Eis →* ℂ :=
  ∏ i ∈ T, coprimalityMask (p i)

theorem markTwist_norm (p : ι → Eis) (T : Finset ι) (x : Eis) : ‖markTwist p T x‖ ≤ 1 := by
  simp only [markTwist, MonoidHom.finsetProd_apply, norm_prod]
  exact Finset.prod_le_one₀ (fun i hi => norm_nonneg _) (fun i hi => coprimalityMask_norm _ _)

theorem markTwist_periodic (p : ι → Eis) (S T : Finset ι) (hTS : T ⊆ S) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {∏ i ∈ S, p i}) (markTwist p T) := by
  intro x y hxy
  simp only [markTwist, MonoidHom.finsetProd_apply]
  apply Finset.prod_congr rfl
  intro i hi
  apply coprimalityMask_periodic (p i) x y
  apply Ideal.mem_span_singleton.mpr
  exact (Finset.dvd_prod_of_mem p (hTS hi)).trans (Ideal.mem_span_singleton.mp hxy)

def markedThetaQuotient (p : ι → Eis) (S : Finset ι) (Ψ : Eis →* ℂ) (c : Eis)
    (x : Eis ⧸ Ideal.span {c}) : ℂ :=
  fixedThetaQuotient Ψ c x * ∏ i ∈ S, if p i ∣ Quotient.out x then 1 else 0

theorem markedThetaQuotient_twists (p : ι → Eis) (S : Finset ι)
    (hp : ∀ i ∈ S, Prime (p i)) (Ψ : Eis →* ℂ) (c : Eis)
    (x : Eis ⧸ Ideal.span {c}) :
    markedThetaQuotient p S Ψ c x =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * fixedThetaQuotient (markTwist p T * Ψ) c x := by
  have hmark (i : ι) (hi : i ∈ S) :
      (if p i ∣ Quotient.out x then (1 : ℂ) else 0) =
        1 - coprimalityMask (p i) (Quotient.out x) := by
    change (if p i ∣ Quotient.out x then (1 : ℂ) else 0) =
      1 - (if IsCoprime (p i) (Quotient.out x) then 1 else 0)
    rw [(hp i hi).coprime_iff_not_dvd]
    by_cases h : p i ∣ Quotient.out x <;> simp [h]
  unfold markedThetaQuotient
  rw [Finset.prod_congr rfl hmark, Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [show markTwist p T * Ψ = Ψ * markTwist p T from mul_comm _ _]
  simp only [fixedThetaQuotient, fixedThetaTwist_mul, markTwist, MonoidHom.finsetProd_apply]
  ring

theorem markedCompletedT_canonical_reflection (p : ι → Eis) (S : Finset ι)
    (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (hΨ : ∀ x, ‖Ψ x‖ ≤ 1)
    (Q : Ideal Eis) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (v0 v1 : ℝ) (hv0 : 0 < v0) (hWs : Function.support W ⊆ Set.Icc v0 v1)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (markedThetaQuotient p S Ψ c) h *
          (finiteTwistCusp c hc h).smoothedKernel W X := by
  have hnorm (T : Finset ι) : ∀ x, ‖(markTwist p T * Ψ) x‖ ≤ 1 := by
    intro x
    rw [MonoidHom.mul_apply, norm_mul]
    exact (mul_le_mul_of_nonneg_right (markTwist_norm p T x) (norm_nonneg _)).trans
      ((one_mul _).le.trans (hΨ x))
  have hper (T : Finset ι) (hT : T ∈ S.powerset) :
      CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i ∈ S, p i})
        (markTwist p T * Ψ) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [markTwist_periodic p S T (Finset.mem_powerset.mp hT) x y (Ideal.mul_le_right hxy),
      hperiod x y (Ideal.mul_le_left hxy)]
  have hcoeff (h : Eis ⧸ Ideal.span {c}) :
      finiteAdditiveFourierCoeff (quotientTrace c hc) (markedThetaQuotient p S Ψ c) h =
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
          finiteAdditiveFourierCoeff (quotientTrace c hc)
            (fixedThetaQuotient (markTwist p T * Ψ) c) h := by
    unfold finiteAdditiveFourierCoeff
    simp_rw [markedThetaQuotient_twists p S hp Ψ c]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc, mul_assoc]
  rw [markedCompletedT_prime_product_twists S p hp Ψ W hWcompact X hX]
  change (∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * completedT (markTwist p T * Ψ) W X) = _
  calc
    _ = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (thetaDerivativeScalar⁻¹ *
        ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc)
          (fixedThetaQuotient (markTwist p T * Ψ) c) h *
            (finiteTwistCusp c hc h).smoothedKernel W X) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [completedT_canonical_smoothed_reflection _ (hnorm T) _ (hper T hT)
        c hc hcQ W v0 v1 hv0 hWs hW X hX]
    _ = _ := by
      simp_rw [hcoeff]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro T hT
      ring

end
end SevenEighths.InverseMoment

end OAI

end Source1388

/- Original source: OAI/NumberTheory/DirichletL/Descent/CuspCongruence.lean; sha256: e3a0e55b221bc2244871314696eb7444d1c03fff21d30215cfbe9b89ba94e32e -/
section Source1389
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open MeasureTheory CompletedGauss CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

private theorem cusp_sum_kernel_integral {ι : Type*} [Fintype ι]
    (d : ι → SourceCuspDatum) (w : ι → ℂ) (F : ℝ → ℂ)
    (hF : ∀ v : ℝ, 0 < v → F v = ∑ i, w i * cuspBarProfile cubicSourceConjugateFunction (d i).point v)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hsupp : Function.support W ⊆ Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (∑ i, w i * (d i).smoothedKernel W X) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        besselSmoothingIntegrand F thetaBesselScale (Vstar W) X ((-1 : ℂ) + t * Complex.I) := by
  let : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let G : ι → ℝ → ℂ := fun i => cuspBarProfile cubicSourceConjugateFunction (d i).point
  let J : ι → ℝ → ℂ := fun i t =>
    besselSmoothingIntegrand (G i) thetaBesselScale (Vstar W) X ((-1 : ℂ) + t * Complex.I)
  have hVs := Vstar_support W lo hi hsupp
  have hV := Vstar_contDiff W lo hi hlo hsupp hW
  have hint (i : ι) : Integrable (J i) :=
    besselSmoothingIntegrand_reflected_integrable (G i) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d i).index (d i).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d i).index) (d i).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d i).heightScale_pos
      (d i).multiplier (d i).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) lo hi hlo hVs hV X hX
  have hline (i : ι) : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, J i t) =
      (d i).smoothedKernel W X :=
    besselSmoothingIntegral_reflected_kernel (G i) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d i).index (d i).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d i).index) (d i).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d i).heightScale_pos
      (d i).multiplier (d i).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) lo hi hlo hVs hV X hX
  have hexpand (t : ℝ) :
      besselSmoothingIntegrand F thetaBesselScale (Vstar W) X ((-1 : ℂ) + t * Complex.I) =
        ∑ i, w i * J i t :=
    besselSmoothingIntegrand_finite_sum F G w hF thetaBesselScale (Vstar W) X _
      (fun i => (d i).cuspBarProfile_mellin_entire.1 _)
  simp_rw [hexpand]
  rw [integral_finsetSum Finset.univ (fun i _ => (hint i).const_mul (w i)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, ← hline]
  ring

theorem cusp_kernel_sum_congr {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι → SourceCuspDatum) (w : ι → ℂ)
    (e : κ → SourceCuspDatum) (z : κ → ℂ)
    (hmult : ∀ n : Eis,
      (∑ i, w i * ShortDraftTrace.breveE (-cuspFrequency n * (d i).point)) =
        ∑ k, z k * ShortDraftTrace.breveE (-cuspFrequency n * (e k).point))
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hsupp : Function.support W ⊆ Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (∑ i, w i * (d i).smoothedKernel W X) = ∑ k, z k * (e k).smoothedKernel W X := by
  let F : ℝ → ℂ := fun v => ∑ i, w i * cuspBarProfile cubicSourceConjugateFunction (d i).point v
  have hprofile (v : ℝ) (hv : 0 < v) :
      F v = ∑ k, z k * cuspBarProfile cubicSourceConjugateFunction (e k).point v := by
    rw [show F v = ∑ i, w i * cuspBarProfile cubicSourceConjugateFunction (d i).point v from rfl,
      ← finiteConjugateSource_wirtingerBar_sum _ _ v hv,
      ← finiteConjugateSource_wirtingerBar_sum _ _ v hv,
      finiteConjugateSource_wirtingerBar, finiteConjugateSource_wirtingerBar]
    simp_rw [hmult]
  rw [cusp_sum_kernel_integral d w F (fun _ _ => rfl) W lo hi hlo hsupp hW X hX,
    cusp_sum_kernel_integral e z F hprofile W lo hi hlo hsupp hW X hX]

theorem markedCompletedT_of_cusp_multiplier {ι κ : Type*} [Fintype κ]
    (p : ι → Eis) (S : Finset ι) (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (hΨ : ∀ x, ‖Ψ x‖ ≤ 1)
    (Q : Ideal Eis) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (d : κ → SourceCuspDatum) (w : κ → ℂ)
    (hmult : ∀ n : Eis, (∑ k, w k * ShortDraftTrace.breveE (-cuspFrequency n * (d k).point)) =
      markedThetaQuotient p S Ψ c (Ideal.Quotient.mk _ n))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ k, w k * (d k).smoothedKernel W X := by
  rw [markedCompletedT_canonical_reflection p S hp Ψ hΨ Q hperiod c hc hcQ
    W hWcompact lo hi hlo hsupp hW X hX]
  congr 1
  apply cusp_kernel_sum_congr (finiteTwistCusp c hc)
    (finiteAdditiveFourierCoeff (quotientTrace c hc)
      (markedThetaQuotient p S Ψ c)) d w ?_ W lo hi hlo hsupp hW X hX
  intro n
  simp_rw [finiteTwistCusp_point]
  rw [thetaFourierTranslation_inversion c hc, hmult]

end
end SevenEighths.InverseMoment

end OAI

end Source1389

/- Original source: OAI/NumberTheory/DirichletL/Descent/MarkedStratum.lean; sha256: b9474e8b49102d57ea7d46c9659b3d8676933ee647f2fc40128ed2d7d5fc12a1 -/
section Source1390
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CubicEisenstein LocalReflectionBrackets CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

section Local
variable {F : Type*} [Field F] [Fintype F]

def markedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ zeroMark h * frequencyMultiplier χ ψ σ ε x h

theorem markedFrequencyRow_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x : F) :
    markedFrequencyRow χ ψ σ ε x 0 = (Fintype.card F : ℂ)⁻¹ := by
  simp [markedFrequencyRow, frequencyMultiplier, finiteAdditiveFourierCoeff, zeroMark]

theorem markedFrequencyRow_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x : F) :
    (∑ h : Fˣ, markedFrequencyRow χ ψ σ ε x h) =
      localReflectionActive zeroMark χ ψ σ ε x := by
  unfold markedFrequencyRow finiteAdditiveFourierCoeff frequencyMultiplier localReflectionActive localFourier
  simp only [Units.ne_zero, ite_false,  Units.val_inv_eq_inv_val,
    Finset.mul_sum, neg_mul]
  apply Finset.sum_congr rfl
  intro h hh
  ring

def mixedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (marked : Bool) (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  if marked then markedFrequencyRow χ ψ σ ε x h else frequencyRow χ ψ j σ ε x h

end Local

noncomputable local instance markedStratumField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) :=
  Ideal.Quotient.field P
noncomputable local instance markedStratumFintype (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) :=
  Fintype.ofFinite _

theorem actual_mixed_frequency_units (P : Ideal Eis) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P) (hc : ringChar (Eis ⧸ P) ≠ 2)
    (ψ : AddChar (Eis ⧸ P) ℂ) (hψ : ψ.IsPrimitive) (marked : Bool)
    (j : ℕ) (hj : j < 6) (σ ε : (Eis ⧸ P)ˣ) (x : Eis ⧸ P) :
    (∑ h : (Eis ⧸ P)ˣ, mixedFrequencyRow (actualSextic P hg) ψ marked j σ ε x h) =
      if marked then
        (rootCard (Eis ⧸ P) : ℂ)⁻¹ * tau (actualSextic P hg) ψ 2 *
          (((actualSextic P hg) ^ 2)⁻¹) ((σ : Eis ⧸ P) * (ε : Eis ⧸ P) * x)
      else (((actualSextic P hg)⁻¹) ^ 2) σ *
        phase (actualSextic P hg) ψ j ε * bracket (actualSextic P hg) j x := by
  cases marked
  · simp only [mixedFrequencyRow, Bool.false_eq_true, ite_false]
    exact canonical_frequencyRow_units P hg hc ψ hψ j hj σ ε x
  · simp only [mixedFrequencyRow, ite_true]
    rw [markedFrequencyRow_units, actual_marked_active_formula P hg hc ψ hψ σ ε x]

theorem actual_mixed_frequency_zero (P : Ideal Eis) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P) (hc : ringChar (Eis ⧸ P) ≠ 2)
    (ψ : AddChar (Eis ⧸ P) ℂ) (marked : Bool)
    (j : ℕ) (hj : j < 6) (σ ε : (Eis ⧸ P)ˣ) (x : Eis ⧸ P) :
    mixedFrequencyRow (actualSextic P hg) ψ marked j σ ε x 0 =
      if marked then (Fintype.card (Eis ⧸ P) : ℂ)⁻¹
      else if j = 0 then 1 - (Fintype.card (Eis ⧸ P) : ℂ)⁻¹ else 0 := by
  cases marked
  · simp only [mixedFrequencyRow, Bool.false_eq_true, ite_false]
    exact canonical_frequencyRow_zero P hg hc ψ j hj σ ε x
  · simp only [mixedFrequencyRow, ite_true]
    exact markedFrequencyRow_zero _ _ _ _ _

theorem actual_mixed_active_stratum {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hc : ∀ i, ringChar (Eis ⧸ P i) ≠ 2)
    (ψ : ∀ i, AddChar (Eis ⧸ P i) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive)
    (marked : ι → Bool) (j : ι → ℕ) (hj : ∀ i, j i < 6)
    (A : Finset ι) (σ ε : ∀ i, (Eis ⧸ P i)ˣ) (x : ∀ i, Eis ⧸ P i) :
    (∑ h ∈ FixedRayActiveSet.activeStratum (fun i => Eis ⧸ P i) A,
      ∏ i, mixedFrequencyRow (actualSextic (P i) (hg i)) (ψ i) (marked i) (j i)
        (σ i) (ε i) (x i) (h i)) =
      (∏ i ∈ A, if marked i then
        (rootCard (Eis ⧸ P i) : ℂ)⁻¹ * tau (actualSextic (P i) (hg i)) (ψ i) 2 *
          (((actualSextic (P i) (hg i)) ^ 2)⁻¹)
            ((σ i : Eis ⧸ P i) * (ε i : Eis ⧸ P i) * x i)
        else (((actualSextic (P i) (hg i))⁻¹) ^ 2) (σ i) *
          phase (actualSextic (P i) (hg i)) (ψ i) (j i) (ε i) *
            bracket (actualSextic (P i) (hg i)) (j i) (x i)) *
      (∏ i ∈ (Finset.univ : Finset ι) \ A,
        if marked i then (Fintype.card (Eis ⧸ P i) : ℂ)⁻¹
        else if j i = 0 then 1 - (Fintype.card (Eis ⧸ P i) : ℂ)⁻¹ else 0) := by
  rw [FixedRayActiveSet.sum_active_stratum]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact actual_mixed_frequency_units (P i) (hg i) (hc i) (ψ i) (hψ i)
      (marked i) (j i) (hj i) (σ i) (ε i) (x i)
  · apply Finset.prod_congr rfl
    intro i hi
    exact actual_mixed_frequency_zero (P i) (hg i) (hc i) (ψ i)
      (marked i) (j i) (hj i) (σ i) (ε i) (x i)

end
end SevenEighths.InverseMoment

end OAI

end Source1390

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActiveCusp.lean; sha256: 1fffb38429c5c83618af0dc16fc842ec940a5ddf6241a15e411e012deb85e38e -/
section Source1391
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance activeQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _

variable {ι : Type*} [Fintype ι]

def localInactiveWeight (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (A : Finset ι) : ℂ :=
  ∏ i ∈ (Finset.univ : Finset ι) \ A,
    finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (F i) 0

def localActiveWeight (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (A : Finset ι) (v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ) : ℂ :=
  ∏ i : A, finiteAdditiveFourierCoeff (quotientTrace (p i.val) (hp i.val)) (F i.val) (v i)

theorem primeFunction_fourier_by_active
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (n : Eis) :
    (∏ i, F i (Ideal.Quotient.mk _ n)) =
      ∑ A : Finset ι, localInactiveWeight p hp F A *
        ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
          localActiveWeight p hp F A v *
            ∏ i : A, quotientTrace (p i.val) (hp i.val)
              ((v i : Eis ⧸ Ideal.span {p i.val}) * Ideal.Quotient.mk _ n) := by
  let (i : ι) : Field (Eis ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  have hpow : (Finset.univ : Finset ι).powerset = (Finset.univ : Finset (Finset ι)) := by
    ext A
    simp
  simpa only [hpow, localInactiveWeight, localActiveWeight] using
    FixedRayActiveSet.fourier_inversion_by_active_set (fun i => Eis ⧸ Ideal.span {p i})
      (fun i => quotientTrace (p i) (hp i))
      (fun i => GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) F
      (fun i => Ideal.Quotient.mk _ n)

theorem activeStratum_function_multiplier
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprimary : ∀ i, λ₀ ^ 2 ∣ p i - 1)
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    {N a0 c0 : Eis} {mode : Bool}
    (D : ∀ A : Finset ι, ControlledStratumArithmetic (fun i : A => p i.val) N a0 c0 mode)
    (hN : (9 : Eis) * c0 ∣ N) (hc0 : c0 ≠ 0)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)) (n : Eis) :
    (∑ A : Finset ι, localInactiveWeight p hp F A *
      ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
        localActiveWeight p hp F A v * ShortDraftTrace.breveE (-cuspFrequency n *
          (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point)) =
      ShortDraftTrace.breveE (-cuspFrequency n * (eisEmbedding a0 / eisEmbedding c0)) *
        ∏ i, F i (Ideal.Quotient.mk _ n) := by
  have hlocal (A : Finset ι) (v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ) :
      ShortDraftTrace.breveE (-cuspFrequency n *
        (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point) =
      ShortDraftTrace.breveE (-cuspFrequency n * (eisEmbedding a0 / eisEmbedding c0)) *
        ∏ i : A, quotientTrace (p i.val) (hp i.val)
          ((v i : Eis ⧸ Ideal.span {p i.val}) * Ideal.Quotient.mk _ n) :=
    (D A).datum_fourier_phase hN
      (primary_finset_product Finset.univ (fun i : A => p i.val) (fun i _ => hprimary i.val))
      hbase s (fun i => hp i.val) hc0 v n
  simp_rw [hlocal]
  rw [primeFunction_fourier_by_active p hp F n]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro v hv
  ring

def fixedActiveFunctionWeight
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (φ : Eis →* ℂ) (t : FixedActiveCuspIndex c p) : ℂ :=
  fixedThetaRowCoeff c hc φ t.1 * localInactiveWeight p hp F t.2.1 *
    localActiveWeight p hp F t.2.1 t.2.2

theorem fixedActiveFunction_multiplier
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprimary : ∀ i, λ₀ ^ 2 ∣ p i - 1)
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (G : ∀ h : Eis ⧸ Ideal.span {c}, FixedFourierGeometry c h) (N : Eis)
    (hN : ∀ h, (9 : Eis) * (G h).c0 ∣ N)
    (D : ∀ h : Eis ⧸ Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => p i.val) N (G h).a0 (G h).c0 (G h).mode)
    (Q : Ideal Eis) (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (φ : Eis →* ℂ) (hφ : CanonicalCoefficientClass.FactorsModulo Q φ) (n : Eis) :
    (∑ t : FixedActiveCuspIndex c p, fixedActiveFunctionWeight p hp F c hc φ t *
      ShortDraftTrace.breveE (-cuspFrequency n *
        (fixedActiveCuspDatum p hp hprimary c G N hN D t).point)) =
      fixedThetaTwist φ n * ∏ i, F i (Ideal.Quotient.mk _ n) := by
  simp only [FixedActiveCuspIndex, Fintype.sum_sigma, fixedActiveFunctionWeight, fixedActiveCuspDatum]
  have hf : (∑ h : Eis ⧸ Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ShortDraftTrace.breveE (-cuspFrequency n * thetaFourierTranslation c h)) = fixedThetaTwist φ n := by
    simp only [fixedThetaRowCoeff]
    rw [thetaFourierTranslation_inversion c hc,
      fixedThetaQuotient_mk φ Q hφ c hcQ]
  rw [← hf, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _ = fixedThetaRowCoeff c hc φ h *
        (∑ A : Finset ι, localInactiveWeight p hp F A *
          ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
            localActiveWeight p hp F A v * ShortDraftTrace.breveE (-cuspFrequency n *
              (activeStratumDatum p hp hprimary (D h) (hN h) (G h).denominator_ne_zero
                (G h).primary (G h).shape A v).point)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := by
      rw [activeStratum_function_multiplier p hp hprimary F (D h) (hN h)
        (G h).denominator_ne_zero (G h).primary (G h).shape n, (G h).point]
      ring

end
end SevenEighths.InverseMoment

end OAI

end Source1391

/- Original source: OAI/NumberTheory/DirichletL/Descent/MixedRow.lean; sha256: 1a27cfa40db90ac7032dae636372ce81de585b28155c51ff51826f61f250e3dd -/
section Source1392
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance mixedQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι]

def unmarkedSexticTwist (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) : Eis →* ℂ where
  toFun n := ∏ i ∈ (Finset.univ : Finset ι) \ S,
    (actualSextic (Ideal.span {p i}) (hg i) ^ j i) (Ideal.Quotient.mk _ n)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, Finset.prod_mul_distrib]

def mixedPrimeFunction (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι)
    (i : ι) (x : Eis ⧸ Ideal.span {p i}) : ℂ :=
  if i ∈ S then zeroMark x else (actualSextic (Ideal.span {p i}) (hg i) ^ j i) x

theorem unmarkedSexticTwist_norm (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (n : Eis) :
    ‖unmarkedSexticTwist p hg j S n‖ ≤ 1 := by
  change ‖∏ i ∈ (Finset.univ : Finset ι) \ S,
    (actualSextic (Ideal.span {p i}) (hg i) ^ j i) (Ideal.Quotient.mk _ n)‖ ≤ 1
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun i hi => norm_nonneg _)
    (fun i hi => FiniteRayExpansion.norm_char_le_one _ _)

theorem unmarkedSexticTwist_periodic (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {∏ i, p i}) (unmarkedSexticTwist p hg j S) := by
  intro x y hxy
  change (∏ i ∈ (Finset.univ : Finset ι) \ S, _) = ∏ i ∈ (Finset.univ : Finset ι) \ S, _
  apply Finset.prod_congr rfl
  intro i hi
  have he : Ideal.Quotient.mk (Ideal.span {p i}) x = Ideal.Quotient.mk _ y := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    exact (Finset.dvd_prod_of_mem p (Finset.mem_univ i)).trans (Ideal.mem_span_singleton.mp hxy)
  rw [he]

theorem mixedPrimeFunction_product (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (n : Eis) :
    (∏ i, mixedPrimeFunction p hg j S i (Ideal.Quotient.mk _ n)) =
      unmarkedSexticTwist p hg j S n * ∏ i ∈ S, if p i ∣ n then 1 else 0 := by
  rw [← Finset.prod_sdiff (Finset.subset_univ S)]
  have hS : (∏ i ∈ S, mixedPrimeFunction p hg j S i (Ideal.Quotient.mk _ n)) =
      ∏ i ∈ S, if p i ∣ n then (1 : ℂ) else 0 := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [mixedPrimeFunction, hi, ite_true, zeroMark,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [hS]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [mixedPrimeFunction, (Finset.mem_sdiff.mp hi).2, ite_false]

omit [Fintype ι] in
theorem markedThetaQuotient_mk (p : ι → Eis) (S : Finset ι)
    (Ψ : Eis →* ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (n : Eis) :
    markedThetaQuotient p S Ψ c (Ideal.Quotient.mk _ n) =
      fixedThetaTwist Ψ n * ∏ i ∈ S, if p i ∣ n then 1 else 0 := by
  unfold markedThetaQuotient
  have hcbase : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q :=
    hcQ.trans (Ideal.mul_mono_right Ideal.mul_le_left)
  rw [fixedThetaQuotient_mk Ψ Q hΨ c hcbase]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hxy : Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) n) - n ∈ Ideal.span {c} :=
    Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {c}) n))
  have hp : p i ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) n) - n :=
    (Finset.dvd_prod_of_mem p hi).trans (Ideal.mem_span_singleton.mp
      (Ideal.mul_le_right (Ideal.mul_le_right (hcQ hxy))))
  simp only [dvd_iff_dvd_of_dvd_sub hp]

end
end SevenEighths.InverseMoment

end OAI

end Source1392

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActiveReflection.lean; sha256: 5aadbea0278a1b41b76c0e7006cd5f164725e26dac5e1c8efbe3cd9b15161165 -/
section Source1393
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open CompletedGauss CubicEisenstein CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance activeReflectionQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem markedCompletedT_fixed_active_strata {ι : Type*} [Fintype ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprime : ∀ i, Prime (p i))
    (hprimary : ∀ i, λ₀ ^ 2 ∣ p i - 1)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι)
    (φ : Eis →* ℂ) (hφnorm : ∀ n, ‖φ n‖ ≤ 1)
    (Q : Ideal Eis) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (G : ∀ h : Eis ⧸ Ideal.span {c}, FixedFourierGeometry c h) (N : Eis)
    (hN : ∀ h, (9 : Eis) * (G h).c0 ∣ N)
    (D : ∀ h : Eis ⧸ Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => p i.val) N (G h).a0 (G h).c0 (G h).mode)
    (call : Eis) (hcall : call ≠ 0) [Fintype (Eis ⧸ Ideal.span {call})]
    (hcallQ : Ideal.span {call} ≤ Ideal.span {(9 : Eis)} *
      ((Q * Ideal.span {∏ i, p i}) * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT (φ * unmarkedSexticTwist p hg j S) W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ t : FixedActiveCuspIndex c p,
        fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ t *
          (fixedActiveCuspDatum p hp hprimary c G N hN D t).smoothedKernel W X := by
  have hnorm (n : Eis) : ‖(φ * unmarkedSexticTwist p hg j S) n‖ ≤ 1 := by
    rw [MonoidHom.mul_apply, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hφnorm n)).trans
      (unmarkedSexticTwist_norm p hg j S n)
  have hperiod : CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i, p i})
      (φ * unmarkedSexticTwist p hg j S) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [hφperiod x y (Ideal.mul_le_left hxy),
      unmarkedSexticTwist_periodic p hg j S x y (Ideal.mul_le_right hxy)]
  apply markedCompletedT_of_cusp_multiplier p S (fun i _ => hprime i) _ hnorm _ hperiod
    call hcall hcallQ (fixedActiveCuspDatum p hp hprimary c G N hN D)
    (fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ) ?_
    W hWcompact lo hi hlo hsupp hW X hX
  intro n
  rw [fixedActiveFunction_multiplier p hp hprimary (mixedPrimeFunction p hg j S)
    c hc G N hN D Q hcQ φ hφperiod,
    markedThetaQuotient_mk p S _ _ hperiod call hcallQ,
    fixedThetaTwist_mul, mixedPrimeFunction_product]
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source1393

/- Original source: OAI/NumberTheory/DirichletL/Descent/ControlledMultiplier.lean; sha256: bd95cbfa7687cf59af140d2edb59adc30c4f9c4db89f552adae216c1720b6e5c -/
section Source1394
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT CubicKubota
open CubicJacobiGlobal ShortDraftCusp FiniteGaussPhase LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance controlledField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis ⧸ P) := Ideal.Quotient.field _
noncomputable local instance controlledFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

theorem controlled_phase_product (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) (x : Eis) :
    star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
        (eisEmbedding c0 * eisEmbedding (∏ i, p i))) =
    (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) (v i) := by
  have hbad : A4BadPhase c0 hc0 (D.matrix v 1 1) D.U x =
      A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x := by
    apply A4BadPhase_eq_of_residue
    convert dvd_mul_of_dvd_left (D.inverse_fixed hN v) D.U using 1 ; ring
  have hlocal := A3_A4_frequency_product p hp hcop hg (D.matrix v 0 0) (D.matrix v 0 1)
    c0 (D.matrix v 1 1) D.U D.w x hc0 (D.determinant v) D.bezout D.sigma D.epsilon
    (fun i => (v i : Eis ⧸ Ideal.span {p i})) (D.frequency_congruence v) D.epsilon_value
  rw [D.relative_character hN hr hbase v, star_mul]
  calc
    _ = star D.fixedFactor * (star (eisEmbedding (symbol (D.matrix v 0 0) (∏ i, p i))) *
        ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
          (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) := by ring
    _ = _ := by rw [hlocal, hbad]; ring

def fullLocalFourierWeight [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) : ℂ :=
  ∏ i, finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (F i) (v i)

theorem controlled_local_multiplier (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (x : Eis) :
    (∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ, fullLocalFourierWeight hp F v *
      star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
        (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) =
    (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, ∑ v : (Eis ⧸ Ideal.span {p i})ˣ,
        finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (F i) v *
          frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
            (quotientTrace (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) v := by
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [mul_assoc, controlled_phase_product D hN hr hbase hp hc0 hcop hg v x]
  simp only [fullLocalFourierWeight, Finset.prod_mul_distrib]
  ring

def mixedActiveBracket [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode)
    (i : ι) (x : Eis) : ℂ :=
  if i ∈ S then
    (rootCard (Eis ⧸ Ideal.span {p i}) : ℂ)⁻¹ *
      tau (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) 2 *
        (((actualSextic (Ideal.span {p i}) (hg i)) ^ 2)⁻¹)
          ((D.sigma i : Eis ⧸ Ideal.span {p i}) * (D.epsilon i : Eis ⧸ Ideal.span {p i}) *
            Ideal.Quotient.mk _ x)
  else (((actualSextic (Ideal.span {p i}) (hg i))⁻¹) ^ 2) (D.sigma i) *
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i) *
      bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x)

theorem mixedActiveBracket_eq_units [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι)
    (D : ControlledStratumArithmetic p N a0 c0 mode) (i : ι) (x : Eis) :
    (∑ v : (Eis ⧸ Ideal.span {p i})ˣ,
      finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (mixedPrimeFunction p hg j S i) v *
        frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
          (quotientTrace (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) v) =
      mixedActiveBracket hp hg j S D i x := by
  have hh := actual_mixed_frequency_units (Ideal.span {p i}) (hg i) (hc i)
    (quotientTrace (p i) (hp i))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i))
    (decide (i ∈ S)) (j i) (hj i) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x)
  have hfun : mixedPrimeFunction p hg j S i = fun t =>
      if i ∈ S then zeroMark t else (actualSextic (Ideal.span {p i}) (hg i) ^ j i) t := rfl
  rw [hfun]
  by_cases hi : i ∈ S
  · simpa only [hi, decide_true, mixedFrequencyRow, mixedPrimeFunction, mixedActiveBracket,
      ite_true, markedFrequencyRow] using hh
  · simpa only [hi, decide_false, mixedFrequencyRow, mixedPrimeFunction, mixedActiveBracket,
      Bool.false_eq_true, ite_false, frequencyRow] using hh

theorem controlled_mixed_multiplier (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι) (x : Eis) :
    (∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
      fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
      star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
        (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) =
    (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, mixedActiveBracket hp hg j S D i x := by
  rw [controlled_local_multiplier D hN hr hbase hp hc0 hcop hg]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact mixedActiveBracket_eq_units hp hg hc j hj S D i x

end
end SevenEighths.InverseMoment

end OAI

end Source1394

/- Original source: OAI/NumberTheory/DirichletL/Descent/ReflectedDual.lean; sha256: 3f3a018f7e9db27b761f245f37a4c27d43da59866e1e4cf701cf8fb347288f79 -/
section Source1395
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups
open CompletedGauss CubicEisenstein ConcreteTraceCRT CubicKubota CompletedDyadic
open CubicJacobiGlobal ShortDraftCusp FiniteGaussPhase LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance dualQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

def mixedSmoothedValue (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
    fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
      (D.datum hN hr hbase s hp hc0 v).smoothedKernel W X

def mixedReflectedValue (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  fixedRadialCoefficientScalar * s.stratumShapeFactor (c0 * ∏ i, p i) *
    ∑' t : ThetaFullIndex,
      (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
        ((ramifiedScale 1 completedRamifiedStep t.2.1 *
          Real.sqrt (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) : ℝ) : ℂ)) *
      CubicReflectionKernel.paperKernel (Vstar W)
        ((X / (27 * (sourceCuspScale s.index) ^ 2 * (Ideal.absNorm (Ideal.span {c0 * ∏ i, p i}) : ℝ) ^ 2)) *
          (ramifiedScale 1 completedRamifiedStep t.2.1) ^ 3 *
          (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) ^ 3) *
      ((star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U
          (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))) *
        ∏ i, mixedActiveBracket hp hg j S D i
          (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))

theorem mixed_smoothed_eq_reflected (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    mixedSmoothedValue D hN hr hbase s hp hc0 hg j S W X =
      mixedReflectedValue D s hp hc0 hg j S W X := by
  have hden : c0 * (∏ i, p i) ≠ 0 :=
    mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hmat (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) :
      (D.sourceGamma hN hr hbase v : SL(2, Eis)) *
        ControlledStratumArithmetic.fixedCusp a0 c0 mode = D.matrix v :=
    D.sourceGamma_mul hN hr hbase v
  have hchar (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) :
      levelTwoComplexCharacter (D.sourceGamma hN hr hbase v) =
        complexCharacter (D.relativeGamma hN hr hbase v) :=
    D.sourceGamma_character hN hr hbase v
  have hC : ∀ v, ((D.sourceGamma hN hr hbase v : SL(2, Eis)) *
      ControlledStratumArithmetic.fixedCusp a0 c0 mode) 1 0 = c0 * ∏ i, p i := by
    intro v
    exact (congrArg (fun M : SL(2, Eis) => M 1 0) (hmat v)).trans (D.denominator v)
  have he := s.sum_smoothedKernel_integral_phase (D.sourceGamma hN hr hbase) _ hden hC
    (fullLocalFourierWeight hp (mixedPrimeFunction p hg j S)) W lo hi hlo hsupp hW X hX
  change mixedSmoothedValue D hN hr hbase s hp hc0 hg j S W X = _ at he
  rw [he]
  unfold mixedReflectedValue
  apply congrArg (fun z : ℂ => fixedRadialCoefficientScalar * s.stratumShapeFactor (c0 * ∏ i, p i) * z)
  apply tsum_congr
  intro t
  congr 1
  simpa only [hchar, hmat, map_mul] using
    controlled_mixed_multiplier D hN hr hbase hp hc0 hcop hg hc j hj S
      (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))

end
end SevenEighths.InverseMoment

end OAI

end Source1395

/- Original source: OAI/NumberTheory/DirichletL/Descent/MarkedPhase.lean; sha256: d91baeb0fda12636400459f90a67b3afa023aaddbd7c4ec7c94fcf1fc9cc4442 -/
section Source1396
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance markedPhaseFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

def markedActiveExponent (S : Finset ι) (j : ι → ℕ) (i : ι) : ℕ := if i ∈ S then 0 else j i

theorem mixedActiveBracket_eq_signed [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode)
    (i : ι) (x : Eis) :
    mixedActiveBracket hp hg j S D i x = (if i ∈ S then (-1 : ℂ) else 1) *
      ((((actualSextic (Ideal.span {p i}) (hg i))⁻¹) ^ 2) (D.sigma i) *
        phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i))
          (markedActiveExponent S j i) (D.epsilon i) *
        bracket (actualSextic (Ideal.span {p i}) (hg i)) (markedActiveExponent S j i)
          (Ideal.Quotient.mk _ x)) := by
  by_cases hi : i ∈ S
  · simp only [mixedActiveBracket, markedActiveExponent, hi,
      phase, bracket, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, inv_pow, map_mul]
    ring
  · simp only [mixedActiveBracket, markedActiveExponent, hi, ite_false, one_mul]

theorem mixedActiveBracket_product [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode) (x : Eis) :
    (∏ i, mixedActiveBracket hp hg j S D i x) =
      (-1 : ℂ) ^ S.card * D.bracketProduct hp hg (markedActiveExponent S j) x := by
  simp_rw [mixedActiveBracket_eq_signed]
  rw [Finset.prod_mul_distrib]
  have hsign : (∏ i : ι, if i ∈ S then (-1 : ℂ) else 1) = (-1 : ℂ) ^ S.card := by
    rw [Finset.prod_ite]
    simp
  rw [hsign]
  rfl

theorem mixedReflectedValue_eq_signed [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) :
    mixedReflectedValue D s hp hc0 hg j S W X =
      (-1 : ℂ) ^ S.card * D.reflectedValue s hp hc0 hg (markedActiveExponent S j) W X := by
  unfold mixedReflectedValue ControlledStratumArithmetic.reflectedValue
  simp_rw [mixedActiveBracket_product]
  conv_rhs => rw [mul_left_comm]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro t
  ring

theorem mixed_model_coefficient [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) :
    s.amplitude u m I J *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c0 hc0
        (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m I J)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m I J)) =
    ((-1 : ℂ) ^ S.card * D.modelRowPhase s hp hg (markedActiveExponent S j) u m) *
      ∑ e : ι → Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0
            (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1) * D.U))
            (s.modelDualNumerator u) u) m I J *
        reflectedBranch (fun i => Ideal.span {p i}) hg (markedActiveExponent S j) e
          (primaryGenerator I) (primaryGenerator J) := by
  rw [mixedActiveBracket_product]
  calc
    _ = (-1 : ℂ) ^ S.card * (s.amplitude u m I J *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c0 hc0
        (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m I J)) *
      D.bracketProduct hp hg (markedActiveExponent S j) (s.modelDualNumerator u m I J)) := by ring
    _ = _ :=
      (congrArg ((-1 : ℂ) ^ S.card * ·)
        (D.model_coefficient s hp hc0 hg (markedActiveExponent S j) u m I J)).trans
          (mul_assoc _ _ _).symm

theorem marked_modelRowPhase_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι) (u : Eisˣ) (m : ℕ) :
    ‖(-1 : ℂ) ^ S.card * D.modelRowPhase s hp hg (markedActiveExponent S j) u m‖ = 1 := by
  have hj' : ∀ i, markedActiveExponent S j i < 6 := by
    intro i
    unfold markedActiveExponent
    split_ifs
    · norm_num
    · exact hj i
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact D.modelRowPhase_norm hN hr hbase s hp hg hchar _ hj' u m

end
end SevenEighths.InverseMoment

end OAI

end Source1396

/- Original source: OAI/NumberTheory/DirichletL/Reflection/Local.lean; sha256: 65f8833c452db19a54061c14d39f19201a163033dd2447b96463bb35c80e1d5b -/
section Source1397
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
open LocalReflectionBrackets
noncomputable section

lemma scalar_inverse_pair (a b c d : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : c*a*b=d) : a⁻¹*b⁻¹ = d⁻¹*c := by
  field_simp
  linear_combination -h

theorem marked_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (B z : F)
    (he : B*z*(σ : F)*(ε : F) = -1) :
    ((χ⁻¹)^2) σ * phase χ ψ 0 ε =
      (-tau χ ψ 2)*(χ (-1))⁻¹^2*(χ B)^2*(χ z)^2 := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  simp only [phase, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte,
    MulChar.pow_apply_coe, MulChar.inv_apply_eq_inv']
  calc
    _ = (-tau χ ψ 2)*((χ σ)⁻¹*(χ ε)⁻¹)^2 := by ring
    _ = _ := by rw [hi]; ring

theorem residual_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A B z : F)
    (hsigma : (σ : F) = A*z) (he : B*z*(σ : F)*(ε : F) = -1) :
    ((χ⁻¹)^2) σ * phase χ ψ 1 ε =
      (tau χ (ψ.mulShift (-1)) 1*tau χ ψ 3)*
        (χ (-1))⁻¹^3*(χ A)*(χ B)^3*(χ z)^4 := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  have hsig : χ (σ : F) = χ A*χ z := by rw [hsigma,map_mul]
  simp only [phase, show (1 : ℕ) ≠ 4 by decide, show (1 : ℕ) ≠ 0 by decide,
    ↓reduceIte, show (1 : ℕ)+2 = 3 by decide,
    MulChar.pow_apply_coe, MulChar.inv_apply_eq_inv']
  have hid : (χ σ)⁻¹^2*(χ ε)⁻¹^3 = (χ σ)*((χ σ)⁻¹*(χ ε)⁻¹)^3 := by
    field_simp
  calc
    _ = (tau χ (ψ.mulShift (-1)) 1*tau χ ψ 3)*((χ σ)⁻¹^2*(χ ε)⁻¹^3) := by ring
    _ = _ := by rw [hid,hi,hsig]; ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1397

/- Original source: OAI/NumberTheory/DirichletL/Reflection/Cofactor.lean; sha256: dbd3024e9f12aabda812471b487f28326e4ca4b610461b6f298245c05e821927 -/
section Source1398
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss ConcreteTraceCRT
open LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance phaseField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance phaseFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def markedPrimeScalar (p c0 : Eis) [hP : (Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  (-tau χ (quotientTrace p hp) 2)*(χ (-1))⁻¹^2*
    (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c0)))^2

def residualPrimeScalar (p c0 : Eis) [hP : (Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  (tau χ ((quotientTrace p hp).mulShift (-1)) 1*tau χ (quotientTrace p hp) 3)*
    (χ (-1))⁻¹^3*(χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c0)))*
      (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c0)))^3

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

theorem controlled_marked_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) 0 (D.epsilon i) =
        markedPrimeScalar (p i) c0 (hp i) (hg i)*
          ∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 2 := by
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  rw [marked_local_phase _ _ _ _ _ _ he]
  change _ = _
  simp only [markedPrimeScalar, cofactor, map_prod, Finset.prod_pow,
    MixedCrossSeparation.crossSymbol]

theorem controlled_residual_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) 1 (D.epsilon i) =
        residualPrimeScalar (p i) c0 (hp i) (hg i)*
          ∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 4 := by
  have hs : (D.sigma i : Eis ⧸ Ideal.span {p i}) =
      Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c0)*Ideal.Quotient.mk _ (cofactor p i) := by
    simpa only [map_mul] using D.sigma_value i
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  rw [residual_local_phase _ _ _ _ _ _ _ hs he]
  simp only [residualPrimeScalar, cofactor, map_prod, Finset.prod_pow,
    MixedCrossSeparation.crossSymbol]

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1398

/- Original source: OAI/NumberTheory/DirichletL/Reflection/Partition.lean; sha256: 6308539e1159338a26a1180d3a31b8eda80406cf9002b5f4e12bafb204f23d95 -/
section Source1399
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
noncomputable section

theorem ordered_cross_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (A B : Finset ι)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    (∏ i, ((∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
      (∏ i ∈ A, ∏ k ∈ B, x i k ^ a * x k i ^ b) := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ A.erase i, x i k ^ a) * (∏ k ∈ B, x i k ^ a) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : Finset.univ.erase i = A.erase i ∪ B := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, ite_eq_left hi, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ B.erase i, x i k ^ b) * (∏ k ∈ A, x i k ^ b) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : Finset.univ.erase i = B.erase i ∪ A := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, ite_eq_right hn, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ a) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k ^ b) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  calc
    _ = (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) *
        (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) := by
      rw [← Finset.prod_union hd, hu]
    _ = _ := by
      rw [hpA, hpB]
      rw [Finset.prod_comm (s := B) (t := A)]
      simp only [Finset.prod_mul_distrib]
      ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1399
