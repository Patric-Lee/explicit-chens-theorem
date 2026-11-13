import OpenAIGrouped.Unit030
import OpenAIGrouped.Unit027
import OpenAIGrouped.Unit028
import OpenAIGrouped.Unit013
import OpenAIGrouped.Unit017

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/WZTransport.lean; sha256: cbe562ae5670bcf00fee19463886fac6ade5c226c20ec9c87956841e302f43e3 -/
section Source1240
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma FirstTail.of_ge_one_fiftieth {S : Finset (Ideal O)} (h : FirstTail (1/4) S)
    {eps : ℝ} (heps : (1/50:ℝ)≤eps) : FirstTail eps S := by
  refine ⟨by linarith,h.norm_four,?_⟩
  simpa only [firstPrimeDefectBound,min_eq_right heps,
    min_eq_right (by norm_num : (1/50:ℝ)≤1/4)] using h.small

private lemma height_integral_wxz (f : HeightSpace→ℂ) (hf : Integrable f heightMeasure) :
    (∫p : HeightSpace,f p ∂heightMeasure)=∫w : ℝ,∫x : ℝ,∫z : ℝ,f ((x,z),w) := by
  rw [integral_prod_symm _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with w hw
  exact integral_prod _ hw

def continuedRowOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
    ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)

theorem continuedRowOnLines_z_transport {K : ℕ}
    (e σ υ l r : ℝ) (he : 0<e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ)
    (hυ : (1/2:ℝ)≤υ) (hl : (17/50:ℝ)≤l) (hlr : l≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ l p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r p ∂heightMeasure := by
  have hi (q : ℝ) (hq : (17/50:ℝ)≤q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ q) heightMeasure :=
    continuedPhysicalRowKernel_integrable e σ υ q he he' hσ hσβ hυ hq S hS hmax hfirst P hP hPS η u hu
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [height_integral_wxz _ (hi l hl),height_integral_wxz _ (hi r (hl.trans hlr))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tw
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tx
  exact first_z_integral_eq (1/4) (by norm_num) S hS
    (hfirst.of_ge_one_fiftieth (by norm_num)) hmax P hPS η u W0 W1 a0 b0 ha0 hW0
    X Y Z hX hZ ((σ:ℂ)+tx*I) ((υ:ℂ)+tw*I) l r hlr
    (by simp;linarith) (by simp;linarith) (by simp;linarith) hl

theorem rowIntegral_wz_transport {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (υ r : ℝ) (hυ : (1/2:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤r) (hr2 : r≤2) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ r) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ r p ∂heightMeasure := by
  have hβ : HeckeZeroSupremum.beta+8*(1/2000:ℝ)≤3 := by linarith [HeckeZeroSupremum.beta_le_one]
  have hi (q : ℝ) (hq : (17/50:ℝ)≤q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ q) heightMeasure :=
    continuedPhysicalRowKernel_integrable (1/2000) 3 υ q (by norm_num) (by norm_num) (by norm_num) hβ hυ hq
      S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  obtain ⟨_,hphysical⟩ := rowIntegral_w_shift (1/2) (by norm_num) (by norm_num) S hS (by norm_num;exact hfirst) hmax P hP hPS
    η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ υ hυ hυ3
  have hinner : (∫q : ℝ×ℝ,shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z υ q ∂(volume.prod volume))=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ 2 p ∂heightMeasure :=
    (integral_prod _ (hi 2 (by norm_num))).symm
  have hz := continuedRowOnLines_z_transport (1/2000) 3 υ r 2 (by norm_num) (by norm_num)
    (by norm_num) hβ hυ hr hr2 S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ
  exact ⟨hi r hr,hphysical.trans (by rw [hinner,hz])⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1240

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/XGrowth.lean; sha256: 92c18f429c4b5b9b659170731cbb8b283cb1bfa254b6e6adad10423b7aded3e1 -/
section Source1241
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem physicalRow_first_x_growth (e eps : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (w z : ℂ) (l r : ℝ)
    (hl : (51/100:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    ∃C : ℝ,0≤C ∧ ∀x : ℂ,l≤x.re → x.re≤r →
      ‖physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|x.im|)^2 := by
  obtain ⟨Cr,hCr,hr⟩ := targetRow_reciprocal_growth e 1 he he' (by norm_num) (by norm_num) S hS.prime
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm r
  let L : ℝ := ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖*
    ‖HeckeOrigin.continued (rowCharacter S hS.prime u) w‖
  let B : ℝ := Cr*(η.modulus.absNorm:ℝ)*N
  have hL : 0≤L := by dsimp [L];positivity
  have hB : 0≤B := by dsimp [B,N];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*B*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro x hxl hxr
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤B*(3+|x.im|)^2 := by
    simpa only [Real.rpow_one] using hr η u x (hlβ.trans hxl)
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh eps S hS hfirst T η u x w z (hl.trans hxl) hw hz (by linarith)
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) r x w z (hl.trans hxl) hxr
      hw hz (by linarith [hfirst.positive])
  unfold physicalCompensatedRow continuedCompensatedRow
  simp only [norm_mul]
  calc
    _ ≤ L*(B*(3+|x.im|)^2)*((Ch*N)*(∏P:T,A P)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hrec hL)
        (mul_le_mul hh' hg (norm_nonneg _) (by dsimp [N];positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1241

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/BufferedContour.lean; sha256: d3d4a0a5426ff7c36b88b462d36d02d13c64ac69cf1a9cd48203d4490a04b9fe -/
section Source1242
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma reciprocal_differentiableAt_of_nonzero (χ : Character) (s : ℂ) (h0 : s≠0)
    (hnz : ¬(χ.residue=1 ∧ s=1) → LFunction χ s≠0) :
    DifferentiableAt ℂ (HeckeReciprocal.reciprocal χ) s := by
  by_cases hχ : χ.residue=1
  · have hr : HeckeReciprocal.regularizedL χ s≠0 := by
      by_cases hs : s=1
      · subst s
        exact HeckeReciprocal.regularizedL_ne_zero_at_one χ hχ
      · rw [HeckeReciprocal.regularizedL_eq χ h0 hs]
        exact mul_ne_zero (sub_ne_zero.mpr hs) (hnz (by simp [hs]))
    have he : HeckeReciprocal.reciprocal χ=(fun z=>(z-1)/HeckeReciprocal.regularizedL χ z) := by
      funext z
      simp only [HeckeReciprocal.reciprocal,ite_eq_left hχ]
    rw [he]
    exact (differentiableAt_id.sub_const 1).div
      (HeckeReciprocal.regularizedL_differentiableAt χ h0) hr
  · have he : HeckeReciprocal.reciprocal χ=(fun z=>(LFunction χ z)⁻¹) := by
      funext z
      simp only [HeckeReciprocal.reciprocal,ite_eq_right hχ]
    rw [he]
    exact (LFunction_differentiableAt χ h0 (Or.inr hχ)).inv (hnz (by simp [hχ]))

theorem physicalCompensatedRow_buffered_differentiableAt_x
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re)
    (hnz : ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
      LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=>physicalCompensatedRow S hS T hT η u x w z) x := by
  have hx0 : x≠0 := by intro h;norm_num [h] at hx
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (reciprocal_differentiableAt_of_nonzero _ x hx0 hnz).const_mul _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_x eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        hx hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_first_differentiableAt_x η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z (by linarith) (by linarith)

lemma sourceMellinWeight_differentiable_x (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) :
    Differentiable ℂ (fun x=>sourceMellinWeight W0 W1 X Y Z x w z) := by
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  unfold sourceMellinWeight
  fun_prop (disch := exact Or.inl hz)

theorem continuedPhysicalRowKernel_buffered_differentiableAt_x {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re)
    (hnz : ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
      LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) x :=
  (((sourceMellinWeight_differentiable_x W0 W1 X Y Z hZ w z) x).mul_const _ |>.mul_const _).mul
    ((physicalCompensatedRow_buffered_differentiableAt_x eps heps S hS hfirst _
      (contourTupleOutside S P hPS) η u x w z hx hw hz hxw hnz).const_mul _)

theorem buffered_x_rectangle {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r T : ℝ)
    (hl : (51/100:ℝ)≤l) (hr : (51/100:ℝ)≤r) (hw : -(1/100:ℝ)≤w.re)
    (hz : (17/50:ℝ)≤z.re) (hlw : 1+eps≤l+w.re) (hrw : 1+eps≤r+w.re)
    (hnz : ∀x∈(uIcc l r ×ℂ uIcc (-T) T),
      ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
        LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    let F := fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -T..T,F ((l:ℂ)+t*I))+
        I*((∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))) := by
  dsimp only
  let F := fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
  have hh : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-T) T) := by
    intro x hx
    have hxlo : min l r≤x.re := hx.1.1
    have hx' : (51/100:ℝ)≤x.re := (le_min hl hr).trans hxlo
    have hxw : 1+eps≤x.re+w.re := by
      have := (le_min (by linarith : 1+eps-w.re≤l) (by linarith : 1+eps-w.re≤r)).trans hxlo
      linarith
    exact (continuedPhysicalRowKernel_buffered_differentiableAt_x eps heps S hS hfirst hmax P hPS η u
      W0 W1 X Y Z hZ x w z hx' hw hz hxw (hnz x hx)).differentiableWithinAt
  have hb := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((l:ℂ)+(-T)*I) ((r:ℂ)+T*I) (by simpa using hh)
  have hc : (∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))+
      I*(∫t : ℝ in -T..T,F ((r:ℂ)+t*I))-I*(∫t : ℝ in -T..T,F ((l:ℂ)+t*I))=0 := by
    simpa [smul_eq_mul] using hb
  have hd := congrArg (fun z : ℂ=>-I*z) hc
  change (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=_
  ring_nf at hd ⊢
  simp only [I_sq] at hd
  linear_combination hd

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1242

/- Original source: OAI/NumberTheory/DirichletL/ContinuationShiftedGaussian.lean; sha256: a0d495d50a5f6d6bb4ddc44f886fddb86c33e9a7798d8d5d8b4854c671e0cd35 -/
section Source1243
namespace OAI

noncomputable section
open MeasureTheory Set Filter Complex
namespace SevenEighths.Continuation

theorem vertical_integral_eq_of_shifted_polynomial_gaussian_bound (F : ℂ→ℂ)
    {a b C : ℝ} (q : ℝ) (n : ℕ) (hab : a≤b)
    (hhol : DifferentiableOn ℂ F {s : ℂ | a≤s.re ∧ s.re≤b})
    (hbound : ∀x∈Icc a b,∀t : ℝ,
      ‖F ((x:ℂ)+t*I)‖≤C*polynomialGaussian n (t+q)) :
    (∫t : ℝ,F ((a:ℂ)+t*I))=∫t : ℝ,F ((b:ℂ)+t*I) := by
  let G : ℂ→ℂ := fun s=>F (s-(q:ℂ)*I)
  have hg : DifferentiableOn ℂ G {s : ℂ | a≤s.re ∧ s.re≤b} := by
    apply hhol.comp (differentiable_id.sub_const ((q:ℂ)*I)).differentiableOn
    intro s hs
    simpa using hs
  have hbnd (x : ℝ) (hx : x∈Icc a b) (t : ℝ) :
      ‖G ((x:ℂ)+t*I)‖≤C*polynomialGaussian n t := by
    have heq : (x:ℂ)+t*I-(q:ℂ)*I=(x:ℂ)+(t-q)*I := by ring
    simpa only [G,heq,sub_add_cancel,Complex.ofReal_sub] using hbound x hx (t-q)
  have hi := vertical_integral_eq_of_polynomial_gaussian_bound G n hab hg hbnd
  have heq (x : ℝ) : (∫t : ℝ,G ((x:ℂ)+t*I))=∫t : ℝ,F ((x:ℂ)+t*I) := by
    have hg' : (fun t : ℝ=>G ((x:ℂ)+t*I))=(fun t : ℝ=>F ((x:ℂ)+(t+(-q))*I)) := by
      funext t
      dsimp [G]
      congr 1
      ring
    rw [hg']
    simpa only [Complex.ofReal_add,Complex.ofReal_neg] using
      (integral_add_right_eq_self (fun t : ℝ=>F ((x:ℂ)+t*I)) (-q) (μ:=volume))
  simpa only [heq] using hi

lemma shifted_height_two (t q : ℝ) :
    (3+|t|)^2≤2*(3+|q|)^2*(1+|t+q|^2) := by
  have ht : |t|≤|t+q|+|q| := by
    calc
      |t|=|(t+q)+(-q)| := by ring_nf
      _ ≤ |t+q|+|-q| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hq : 0≤|q| := abs_nonneg _
  have hu : 0≤|t+q| := abs_nonneg _
  have hb : (3+|t|)^2≤(3+|q|+|t+q|)^2 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hs := sq_nonneg ((3+|q|)-|t+q|)
  have hm : 0≤((3+|q|)^2-1)*|t+q|^2 := mul_nonneg (by nlinarith) (sq_nonneg _)
  nlinarith

end SevenEighths.Continuation

end

end OAI

end Source1243

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/XBoundary.lean; sha256: 11e4b4eeed42e817f3796efcf19f158b72b27ae2e2ace1272dd7b8d48dca075c -/
section Source1244
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def xRowScalar {K : ℕ} (P : Fin K→PrimeIdeal) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y : ℝ) (w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Y:ℂ)^(w-1)*
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*mellin W1 w*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

lemma continuedPhysicalRowKernel_x_factor {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      xRowScalar P u W0 W1 X Y w z*(Z:ℂ)^(x+z-1)*Complex.exp ((x+z-1)^2)*
        (star ((calibrationForSet S hmax).residueMonoid u.val)*
          physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z) := by
  unfold continuedPhysicalRowKernel xRowScalar sourceMellinWeight
  ring

lemma coupled_gaussian_bound (z : ℂ) {l r v : ℝ} (hl : 0<l) (hv : v∈Icc l r) (t : ℝ) :
    ‖Complex.exp ((((v:ℂ)+t*I)+z-1)^2)‖≤
      Real.exp ((|z.re|+r+1)^2)*Real.exp (-((t+z.im)^2)) := by
  rw [Complex.norm_exp,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : ((((v:ℂ)+t*I)+z-1)^2).re=(v+z.re-1)^2-(t+z.im)^2 := by simp [pow_two]
  rw [hre]
  have hvp : 0<v := hl.trans_le hv.1
  have hA : |v+z.re-1|≤|z.re|+r+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le z.re,le_abs_self z.re,hv.2]
  have hh := pow_le_pow_left₀ (abs_nonneg (v+z.re-1)) hA 2
  rw [sq_abs] at hh
  linarith

theorem continuedPhysicalRowKernel_x_gaussian {K : ℕ}
    (e eps : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r : ℝ)
    (hl : (51/100:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    ∃B : ℝ,0≤B ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((v:ℂ)+t*I) w z‖≤
        B*Continuation.polynomialGaussian 2 (t+z.im) := by
  obtain ⟨C,hC,hrow⟩ := physicalRow_first_x_growth e eps he he' S hS hfirst _
    (contourTupleOutside S P hPS) η u w z l r hl hlβ hw hz hlw
  let A := ‖xRowScalar P u W0 W1 X Y w z‖*scaleBound Z (l+z.re-1) (r+z.re-1)*
    Real.exp ((|z.re|+r+1)^2)*C
  have hA : 0≤A := by dsimp [A,scaleBound];positivity
  refine ⟨A*(2*(3+|z.im|)^2),by positivity,?_⟩
  intro v hv t
  have hZb := cpow_le_scaleBound hZ (((v:ℂ)+t*I)+z-1)
    (show (((v:ℂ)+t*I)+z-1).re∈Icc (l+z.re-1) (r+z.re-1) by
      simpa using And.intro (by linarith [hv.1] : l+z.re-1≤v+z.re-1)
        (by linarith [hv.2] : v+z.re-1≤r+z.re-1))
  have hgb := coupled_gaussian_bound z (by linarith : 0<l) hv t
  have hr : ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u ((v:ℂ)+t*I) w z‖≤C*(3+|t|)^2 := by
    rw [norm_mul,norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _)
      ((calibrationForSet S hmax).residueMonoid_norm_le_one _)).trans
    simpa using hrow ((v:ℂ)+t*I) (by simpa using hv.1) (by simpa using hv.2)
  rw [continuedPhysicalRowKernel_x_factor,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (‖xRowScalar P u W0 W1 X Y w z‖*scaleBound Z (l+z.re-1) (r+z.re-1))*
        (Real.exp ((|z.re|+r+1)^2)*Real.exp (-((t+z.im)^2)))*(C*(3+|t|)^2) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hZb (norm_nonneg _)) hgb
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (scaleBound_pos _ _ _).le))
        hr (norm_nonneg _) (by unfold scaleBound;positivity)
    _ = A*(3+|t|)^2*Real.exp (-((t+z.im)^2)) := by dsimp [A];ring
    _ ≤ A*(2*(3+|z.im|)^2*(1+|t+z.im|^2))*Real.exp (-((t+z.im)^2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Continuation.shifted_height_two t z.im) hA) (Real.exp_pos _).le
    _ = _ := by unfold Continuation.polynomialGaussian;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1244

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/XShift.lean; sha256: d05a3394d1093f618ccf9df0b1dcbac0b7d789eac8e0aedf4396891f2e10a1de -/
section Source1245
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem first_x_integral_eq {K : ℕ}
    (e eps : ℝ) (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r : ℝ) (hlr : l≤r)
    (hl : (51/100:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((l:ℂ)+t*I) w z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((r:ℂ)+t*I) w z := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_x_gaussian e (eps/2) he he' S hS hfirst hmax P hPS
    η u W0 W1 X Y Z hZ w z l r hl hlβ hw hz (by linarith)
  apply Continuation.vertical_integral_eq_of_shifted_polynomial_gaussian_bound
    (fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) z.im 2 hlr _ hbound
  intro x hx
  apply (continuedPhysicalRowKernel_buffered_differentiableAt_x eps heps S hS hfirst hmax P hPS η u
    W0 W1 X Y Z hZ x w z (hl.trans hx.1) hw hz (by linarith [hx.1]) ?_).differentiableWithinAt
  intro hpole
  exact HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt _ (by linarith [hx.1]) (by tauto)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1245

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/SourceTransport.lean; sha256: ddd8d670a8d834de62f39679d8457c0d8a1827f39d51f31a789a71e3ec066523 -/
section Source1246
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

private lemma height_integral_wzx (f : HeightSpace→ℂ) (hf : Integrable f heightMeasure) :
    (∫p : HeightSpace,f p ∂heightMeasure)=∫w : ℝ,∫z : ℝ,∫x : ℝ,f ((x,z),w) := by
  rw [integral_prod_symm _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with w hw
  exact integral_prod_symm _ hw

theorem continuedRowOnLines_x_transport {K : ℕ}
    (e l r υ ξ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hl : (7/8:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l) (hlr : l≤r)
    (hυ : (1/2:ℝ)≤υ) (hξ : (17/50:ℝ)≤ξ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z l υ ξ p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z r υ ξ p ∂heightMeasure := by
  have hi (q : ℝ) (hq : l≤q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z q υ ξ) heightMeasure :=
    continuedPhysicalRowKernel_integrable e q υ ξ he he' (hl.trans hq) (hlβ.trans hq) hυ hξ
      S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [height_integral_wzx _ (hi l le_rfl),height_integral_wzx _ (hi r hlr)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tw
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tz
  exact first_x_integral_eq e (1/4) he he' (by norm_num) S hS
    (hfirst.of_ge_one_fiftieth (by norm_num)) hmax P hPS η u W0 W1 X Y Z hZ
    ((υ:ℂ)+tw*I) ((ξ:ℂ)+tz*I) l r hlr (by linarith) hlβ
    (by simp;linarith) (by simpa using hξ) (by simp;linarith)

theorem rowIntegral_source_lines {K : ℕ}
    (e σ υ r : ℝ) (he : 0<e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ) (hσ3 : σ≤3)
    (hυ : (1/2:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r p ∂heightMeasure := by
  have hi := continuedPhysicalRowKernel_integrable e σ υ r he he' hσ hσβ hυ hr
    S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  obtain ⟨_,hphysical⟩ := rowIntegral_wz_transport S hS hmax hfirst P hP hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ υ 2 hυ hυ3 (by norm_num) le_rfl
  have hβ3 : HeckeZeroSupremum.beta+8*e≤3 := hσβ.trans hσ3
  have hz : (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ r p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ 2 p ∂heightMeasure := by
    by_cases hr2 : r≤2
    · exact continuedRowOnLines_z_transport e 3 υ r 2 he he' (by norm_num) hβ3 hυ hr hr2
        S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    · exact (continuedRowOnLines_z_transport e 3 υ 2 r he he' (by norm_num) hβ3 hυ (by norm_num) (le_of_not_ge hr2)
        S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).symm
  have hx := continuedRowOnLines_x_transport e σ 3 υ r he he' hσ hσβ hσ3 hυ hr
    S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  exact ⟨hi,hphysical.trans (by rw [hx,hz])⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1246

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/PhysicalDyad.lean; sha256: e1745d3c5f6464d88e7b408d91dfe01b5395f53a46e2a805313e5addad6427f5 -/
section Source1247
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def finitePhysicalRows {K : ℕ} (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset PrimeIdeal)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val.val) W0 W1 X Y Z u

def weightedRowOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
    frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩*
    calibratedTupleValue S hS hmax η u P hPS W Yp
      ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)

lemma weightedRowOnLines_eq {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) :
    weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ υ r t=
      (∏i,W i (((P i).val.absNorm:ℝ)/Yp i))*
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r t := by
  have hnorm (i : Fin K) : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)=
      ((P i).val.absNorm:ℂ) := by
    rw [primaryTuple_norm (P i) (outside_prime_supported S hS.bad (P i) (hPS i))]
    norm_cast
  unfold weightedRowOnLines continuedRowOnLines continuedPhysicalRowKernel calibratedTupleValue
  simp only [hnorm,Finset.prod_mul_distrib]
  ring

section
variable {K : ℕ} (e σ υ r : ℝ) (he : 0<e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ) (hσ3 : σ≤3)
    (hυ : (1/2:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)

include he he' hσ hσβ hσ3 hυ hυ3 hr hfirst hR hdis ha0 ha1 hW0 hW1 hX hY hZ in
theorem finitePhysicalRows_eq_integral :
    Integrable (fun t : HeightSpace=>∑u∈R,∑P:(∀i,T i),
      weightedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
        η u W Yp W0 W1 X Y Z σ υ r t) heightMeasure ∧
    finitePhysicalRows S hmax η R T W Yp W0 W1 X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫t : HeightSpace,(∑u∈R,∑P:(∀i,T i),
          weightedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
            η u W Yp W0 W1 X Y Z σ υ r t) ∂heightMeasure := by
  let f (u : FreeRow) (P : ∀i,T i) := weightedRowOnLines S hS hmax
    (fun i=>(P i).val) (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z σ υ r
  have hsource (u : FreeRow) (hu : u∈R) (P : ∀i,T i) := rowIntegral_source_lines e σ υ r he he' hσ hσβ hσ3 hυ hυ3 hr
    S hS hmax hfirst (fun i=>(P i).val) (hdis P) (fun i=>hT i _ (P i).property) η u (hR u hu)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hfi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : Integrable (f u P) heightMeasure := by
    have heq : f u P=(fun t=>(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
        continuedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
          η u W0 W1 X Y Z σ υ r t) := by
      funext t
      exact weightedRowOnLines_eq S hS hmax _ _ η u W Yp W0 W1 X Y Z σ υ r t
    rw [heq]
    exact (hsource u hu P).1.const_mul _
  have hiu (u : FreeRow) (hu : u∈R) : Integrable (fun t=>∑P:(∀i,T i),f u P t) heightMeasure :=
    integrable_finsetSum _ (fun P hP=>hfi u hu P)
  have hi : Integrable (fun t=>∑u∈R,∑P:(∀i,T i),f u P t) heightMeasure :=
    integrable_finsetSum _ hiu
  refine ⟨hi,?_⟩
  change finitePhysicalRows S hmax η R T W Yp W0 W1 X Y Z=_*(∫t,∑u∈R,∑P:(∀i,T i),f u P t ∂heightMeasure)
  rw [integral_finsetSum R hiu]
  unfold finitePhysicalRows
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun P hP=>hfi u hu P),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [(hsource u hu P).2]
  have hi' : (∫t,f u P t ∂heightMeasure)=
      (∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
        ∫t,continuedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
          η u W0 W1 X Y Z σ υ r t ∂heightMeasure := by
    simp_rw [f,weightedRowOnLines_eq]
    exact integral_const_mul _ _
  rw [hi']
  ring

include he he' hσ hσβ hσ3 hυ hυ3 hr hfirst hR hdis ha0 ha1 hW0 hW1 hX hY hZ in
theorem norm_finitePhysicalRows_le_absolute :
    ‖finitePhysicalRows S hmax η R T W Yp W0 W1 X Y Z‖≤
      ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*
        absolutePhysicalDyadIntegral S hS hmax η R T hT W Yp W0 W1 X Y Z σ υ r := by
  let f (u : FreeRow) (P : ∀i,T i) := weightedRowOnLines S hS hmax
    (fun i=>(P i).val) (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z σ υ r
  have hfi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : Integrable (f u P) heightMeasure := by
    have hi := continuedPhysicalRowKernel_integrable e σ υ r he he' hσ hσβ hυ hr S hS hmax hfirst
      (fun i=>(P i).val) (hdis P) (fun i=>hT i _ (P i).property) η u (hR u hu)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    have heq : f u P=(fun t=>(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
        continuedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
          η u W0 W1 X Y Z σ υ r t) := by
      funext t
      exact weightedRowOnLines_eq S hS hmax _ _ η u W Yp W0 W1 X Y Z σ υ r t
    rw [heq]
    exact hi.const_mul _
  let g (t : HeightSpace) := ‖sourceMellinWeight W0 W1 X Y Z
      ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)‖*
    physicalDyadNorm S hS hmax η R T hT W Yp
      ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
  have hg (t : HeightSpace) : (∑u∈R,∑P:(∀i,T i),‖f u P t‖)=g t := by
    simp only [f,g,weightedRowOnLines,physicalDyadNorm,norm_mul,Finset.mul_sum,mul_assoc]
  have hgi : Integrable g heightMeasure := by
    have hh : Integrable (fun t=>∑u∈R,∑P:(∀i,T i),‖f u P t‖) heightMeasure :=
      integrable_finsetSum R (fun u hu=>integrable_finsetSum Finset.univ (fun P hP=>(hfi u hu P).norm))
    exact hh.congr (Filter.Eventually.of_forall hg)
  obtain ⟨hi,heq⟩ := finitePhysicalRows_eq_integral e σ υ r he he' hσ hσβ hσ3 hυ hυ3 hr S hS hmax
    hfirst η R hR T hT hdis W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hp (t : HeightSpace) : ‖∑u∈R,∑P:(∀i,T i),f u P t‖≤g t := by
    rw [←hg]
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun u hu=>norm_sum_le _ _)
  rw [heq,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_integral_le_integral_norm _).trans (integral_mono hi.norm hgi hp)

end
end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1247

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/PhysicalLargeTail.lean; sha256: 0bfd3653b3882b7ea4a6708e3b68ef0bbf8709066fa9c753795a3299949fcbee -/
section Source1248
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem large_original_physical_tail (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((13/16:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨r,C,hr,hC,hmain⟩ := large_physical_tail_arbitrary_saving K δ a b B ζ saving hδ hδ' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hgs,hgb⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let f : ℕ→ℂ := fun n=>finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
  let g : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r
  have hbnd (n : ℕ) : ‖f n‖≤N*g n := norm_finitePhysicalRows_le_absolute
    (1/2000) 2 2 r (by norm_num) (by norm_num) (by norm_num)
    (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num) (by norm_num) (by norm_num) hr
    S hS hmax hfirst η (R n) (fun u hu=>(hR n u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  have hns : Summable (fun n=>‖f n‖) := Summable.of_nonneg_of_le (fun n=>norm_nonneg _) hbnd (hgs.mul_left N)
  refine ⟨hns.of_norm,?_⟩
  calc
    (∑'n,‖f n‖) ≤ ∑'n,N*g n := hns.tsum_le_tsum hbnd (hgs.mul_left N)
    _ = N*(∑'n,g n) := tsum_mul_left
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving)) := mul_le_mul_of_nonneg_left hgb hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source1248

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/RowPartition.lean; sha256: 5433506b2b0efcf82066fabbee2e121f64126f997f9fef0bc090ccce2971ab6b -/
section Source1249
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def rowNorm (u : FreeRow) : ℝ := (Ideal.span {u.val}:Ideal O).absNorm

lemma rowNorm_ge_one (u : FreeRow) : 1≤rowNorm u := by
  unfold rowNorm
  have hn : (Ideal.span {u.val}:Ideal O)≠⊥ := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn)

lemma finite_bounded_freeRows (H : ℝ) : {u : FreeRow | rowNorm u≤H}.Finite := by
  by_contra hs
  obtain ⟨n,hn⟩ := exists_nat_gt (128*max 1 H)
  have hinf : Set.Infinite {u : FreeRow | rowNorm u≤H} := hs
  obtain ⟨T,hT,hcard⟩ := hinf.exists_subset_card_eq n
  have hc := freeRow_count T (max 1 H) (le_max_left _ _) (fun u hu=>(hT hu).trans (le_max_right _ _))
  rw [hcard] at hc
  exact not_le_of_gt hn hc

def boundedFreeRows (H : ℝ) : Finset FreeRow := (finite_bounded_freeRows H).toFinset

@[simp] lemma mem_boundedFreeRows {H : ℝ} {u : FreeRow} : u∈boundedFreeRows H ↔ rowNorm u≤H :=
  Set.Finite.mem_toFinset _

def rowBand (A B : ℝ) : Finset FreeRow := (boundedFreeRows B).filter (fun u=>u.val≠1 ∧ A≤rowNorm u ∧ rowNorm u<B)

@[simp] lemma mem_rowBand {A B : ℝ} {u : FreeRow} :
    u∈rowBand A B ↔ u.val≠1 ∧ A≤rowNorm u ∧ rowNorm u<B := by
  simp only [rowBand,Finset.mem_filter,mem_boundedFreeRows]
  constructor
  · exact And.right
  · intro h
    exact ⟨h.2.2.le,h⟩

def dyadicRows (A : ℝ) (n : ℕ) : Finset FreeRow := rowBand (A*(2:ℝ)^n) (A*(2:ℝ)^(n+1))

lemma mem_dyadicRows {A : ℝ} {n : ℕ} {u : FreeRow} :
    u∈dyadicRows A n ↔ u.val≠1 ∧ A*(2:ℝ)^n≤rowNorm u ∧ rowNorm u<2*(A*(2:ℝ)^n) := by
  simp only [dyadicRows,mem_rowBand,pow_succ]
  ring_nf

lemma dyadicRows_disjoint (A : ℝ) (hA : 0<A) : Pairwise (fun m n=>Disjoint (dyadicRows A m) (dyadicRows A n)) := by
  intro m n hmn
  apply Finset.disjoint_left.mpr
  intro u hm hn
  rw [mem_dyadicRows] at hm hn
  have hpow (j k : ℕ) (hjk : j<k) : 2*(A*(2:ℝ)^j)≤A*(2:ℝ)^k := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.succ_le_iff.mpr hjk)
    have := mul_le_mul_of_nonneg_left hh hA.le
    simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using this
  rcases lt_or_gt_of_ne hmn with h|h
  · exact not_lt_of_ge ((hpow m n h).trans hn.2.1) hm.2.2
  · exact not_lt_of_ge ((hpow n m h).trans hm.2.1) hn.2.2

lemma exists_dyadicRows (A : ℝ) (hA : 0<A) (u : FreeRow) (hu : u.val≠1) (hU : A≤rowNorm u) :
    ∃n : ℕ,u∈dyadicRows A n := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near ((le_div_iff₀ hA).mpr (by simpa using hU)) (by norm_num : (1:ℝ)<2)
  refine ⟨n,mem_dyadicRows.mpr ⟨hu,?_,?_⟩⟩
  · have hh := (le_div_iff₀ hA).mp hn
    simpa only [mul_comm] using hh
  · have hh := (div_lt_iff₀ hA).mp hn'
    simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hh

def dyadicRowEquiv (A : ℝ) (hA : 0<A) :
    (Σn : ℕ,dyadicRows A n) ≃ {u : FreeRow // u.val≠1 ∧ A≤rowNorm u} :=
  Equiv.ofBijective (fun p=>⟨p.2.val,(mem_dyadicRows.mp p.2.property).1,
    (le_mul_of_one_le_right hA.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))).trans (mem_dyadicRows.mp p.2.property).2.1⟩) (by
    constructor
    · rintro ⟨m,u⟩ ⟨n,v⟩ heq
      have huv : u.val=v.val := congrArg Subtype.val heq
      have hmn : m=n := by
        by_contra h
        exact (Finset.disjoint_left.mp (dyadicRows_disjoint A hA h)) u.property (huv.symm ▸ v.property)
      subst n
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext huv))
    · intro u
      obtain ⟨n,hn⟩ := exists_dyadicRows A hA u.val u.property.1 u.property.2
      exact ⟨⟨n,⟨u.val,hn⟩⟩,rfl⟩)

theorem tsum_dyadicRows (A : ℝ) (hA : 0<A) (f : FreeRow→ℂ) (hf : Summable f) :
    Summable (fun n=>∑u∈dyadicRows A n,f u) ∧
      (∑'u : FreeRow,if u.val≠1 ∧ A≤rowNorm u then f u else 0)=
        ∑'n : ℕ,∑u∈dyadicRows A n,f u := by
  let e := dyadicRowEquiv A hA
  have hs : Summable (fun p : Σn : ℕ,dyadicRows A n=>f p.2.val) :=
    e.summable_iff.mpr (hf.subtype (fun u=>u.val≠1 ∧ A≤rowNorm u))
  have heq : (fun n : ℕ=>∑'u : dyadicRows A n,f u.val)=(fun n=>∑u∈dyadicRows A n,f u) := by
    funext n
    exact Finset.tsum_subtype _ _
  refine ⟨by simpa only [heq] using hs.sigma,?_⟩
  calc
    _ = ∑'u : {u : FreeRow // u.val≠1 ∧ A≤rowNorm u},f u.val := by
      have hh := (tsum_subtype {u : FreeRow | u.val≠1 ∧ A≤rowNorm u} f).symm
      convert hh using 1
      · apply tsum_congr
        intro u
        by_cases h : u.val≠1 ∧ A≤rowNorm u
        · simp [h]
        · simp [h]
      · rfl
    _ = ∑'p : Σn : ℕ,dyadicRows A n,f p.2.val := (e.tsum_eq (fun u=>f u.val)).symm
    _ = _ := by rw [hs.tsum_sigma];simp_rw [Finset.tsum_subtype]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1249

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/SmallPartition.lean; sha256: dab48be821995c28f6cf8e57afbd1451c99bd3216875e4b3ce0a835c4bff9322 -/
section Source1250
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

def smallDyadicIndices (L : ℝ) : Finset ℕ :=
  (Finset.range (Nat.find (pow_unbounded_of_one_lt L (by norm_num : (1:ℝ)<2)))).filter (fun n=>(2:ℝ)^n≤L)

@[simp] lemma mem_smallDyadicIndices {L : ℝ} {n : ℕ} : n∈smallDyadicIndices L ↔ (2:ℝ)^n≤L := by
  simp only [smallDyadicIndices,Finset.mem_filter,Finset.mem_range]
  constructor
  · exact And.right
  · intro hn
    refine ⟨?_,hn⟩
    by_contra h
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (not_lt.mp h)
    exact not_lt_of_ge (hp.trans hn) (Nat.find_spec (pow_unbounded_of_one_lt L (by norm_num : (1:ℝ)<2)))

def smallDyadicRows (L : ℝ) (n : ℕ) : Finset FreeRow := (dyadicRows 1 n).filter (fun u=>rowNorm u<L)

@[simp] lemma mem_smallDyadicRows {L : ℝ} {n : ℕ} {u : FreeRow} :
    u∈smallDyadicRows L n ↔ u∈dyadicRows 1 n ∧ rowNorm u<L := Finset.mem_filter

lemma smallDyadicRows_disjoint (L : ℝ) : Pairwise (fun m n=>Disjoint (smallDyadicRows L m) (smallDyadicRows L n)) := by
  intro m n hmn
  exact (dyadicRows_disjoint 1 (by norm_num) hmn).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

lemma smallDyadicRows_eq_empty {L : ℝ} {n : ℕ} (hn : n∉smallDyadicIndices L) : smallDyadicRows L n=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have h := mem_smallDyadicRows.mp hu
  have hlo := (mem_dyadicRows.mp h.1).2.1
  apply hn
  rw [mem_smallDyadicIndices]
  simpa only [one_mul] using hlo.trans h.2.le

lemma small_rows_biUnion (L : ℝ) :
    (smallDyadicIndices L).biUnion (smallDyadicRows L)=rowBand 1 L := by
  ext u
  constructor
  · intro hu
    obtain ⟨n,hn,hu⟩ := Finset.mem_biUnion.mp hu
    have hh := mem_smallDyadicRows.mp hu
    have hm := mem_dyadicRows.mp hh.1
    exact mem_rowBand.mpr ⟨hm.1,rowNorm_ge_one u,hh.2⟩
  · intro hu
    have hh := mem_rowBand.mp hu
    obtain ⟨n,hn⟩ := exists_dyadicRows 1 (by norm_num) u hh.1 hh.2.1
    refine Finset.mem_biUnion.mpr ⟨n,?_,mem_smallDyadicRows.mpr ⟨hn,hh.2.2⟩⟩
    rw [mem_smallDyadicIndices]
    have hlo := (mem_dyadicRows.mp hn).2.1
    simpa only [one_mul] using hlo.trans hh.2.2.le

lemma sum_small_dyadicRows (L : ℝ) (f : FreeRow→ℂ) :
    (∑u∈rowBand 1 L,f u)=∑n∈smallDyadicIndices L,∑u∈smallDyadicRows L n,f u := by
  rw [←small_rows_biUnion L]
  exact Finset.sum_biUnion (fun m hm n hn hmn=>smallDyadicRows_disjoint L hmn)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1250

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/ExhaustivePartition.lean; sha256: 64f6cdf6a0948d07fa64651ede430f8da4feb0f6567d92830564a83d929333fb -/
section Source1251
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

theorem nonprincipal_rows_partition (L U : ℝ) (hL : 1≤L) (hLU : L≤U)
    (f : FreeRow→ℂ) (hf : Summable f) :
    (∑'u : FreeRow,if u.val=1 then 0 else f u)=
      (∑n∈smallDyadicIndices L,∑u∈smallDyadicRows L n,f u)+
        (∑u∈rowBand L U,f u)+(∑'n : ℕ,∑u∈dyadicRows U n,f u) := by
  let g1 := (↑(rowBand 1 L):Set FreeRow).indicator f
  let g2 := (↑(rowBand L U):Set FreeRow).indicator f
  let g3 := {u : FreeRow | u.val≠1 ∧ U≤rowNorm u}.indicator f
  have hg1 : Summable g1 := hf.indicator _
  have hg2 : Summable g2 := hf.indicator _
  have hg3 : Summable g3 := hf.indicator _
  have hpoint (u : FreeRow) : (if u.val=1 then 0 else f u)=g1 u+g2 u+g3 u := by
    have hnorm := rowNorm_ge_one u
    by_cases hu : u.val=1
    · simp [g1,g2,g3,mem_rowBand,hu]
    · by_cases hsmall : rowNorm u<L
      · have hU : ¬U≤rowNorm u := not_le.mpr (hsmall.trans_le hLU)
        have hL' : ¬L≤rowNorm u := not_le.mpr hsmall
        simp [g1,g2,g3,mem_rowBand,hu,hnorm,hsmall,hL',hU]
      · have hL' : L≤rowNorm u := le_of_not_gt hsmall
        by_cases hlarge : U≤rowNorm u
        · have hU : ¬rowNorm u<U := not_lt.mpr hlarge
          simp [g1,g2,g3,mem_rowBand,hu,hnorm,hsmall,hL',hlarge,hU]
        · have hU : rowNorm u<U := lt_of_not_ge hlarge
          simp [g1,g2,g3,mem_rowBand,hu,hnorm,hsmall,hL',hlarge,hU]
  have hsum1 : (∑'u,g1 u)=∑u∈rowBand 1 L,f u := by
    rw [tsum_eq_sum (s:=rowBand 1 L) (fun u hu=>Set.indicator_of_notMem hu f)]
    apply Finset.sum_congr rfl
    intro u hu
    exact Set.indicator_of_mem hu f
  have hsum2 : (∑'u,g2 u)=∑u∈rowBand L U,f u := by
    rw [tsum_eq_sum (s:=rowBand L U) (fun u hu=>Set.indicator_of_notMem hu f)]
    apply Finset.sum_congr rfl
    intro u hu
    exact Set.indicator_of_mem hu f
  have hsum3 : (∑'u,g3 u)=∑'n : ℕ,∑u∈dyadicRows U n,f u := by
    have hh := (tsum_dyadicRows U (by linarith) f hf).2
    convert hh using 1
    apply tsum_congr
    intro u
    by_cases h : u.val≠1 ∧ U≤rowNorm u <;> simp [g3,h]
  simp_rw [hpoint]
  rw [(hg1.add hg2).tsum_add hg3,hg1.tsum_add hg2,hsum1,hsum2,hsum3,sum_small_dyadicRows]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1251

/- Original source: OAI/NumberTheory/DirichletL/Detector/CanonicalSlots.lean; sha256: cf76e96ad7d4dc321672fd86cdaacd3d75212497aca7100ae61de70d824853d1 -/
section Source1252
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def canonicalSlotSupport (T : Finset PrimeIdeal) : Finset O :=
  T.image (fun P=>primaryGenerator P.val)

lemma primaryPrime_injective {P Q : PrimeIdeal} (hP : Supported P.val) (hQ : Supported Q.val)
    (h : primaryGenerator P.val=primaryGenerator Q.val) : P=Q := by
  apply Subtype.ext
  have hh := congrArg (fun a : O=>Ideal.span {a}) h
  simpa only [span_primaryGenerator_of_supported _ hP,span_primaryGenerator_of_supported _ hQ] using hh

lemma canonicalSlotSupport_nonzero (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (a : O) (ha : a∈canonicalSlotSupport T) : a≠0 := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp ha
  exact supported_primaryGenerator_ne_zero P.val (hT P hP)

def canonicalSlotEquiv (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val) :
    ↥T ≃ ↥(canonicalSlotSupport T) :=
  Equiv.ofBijective
    (fun P=>⟨primaryGenerator P.val.val,Finset.mem_image.mpr ⟨P.val,P.property,rfl⟩⟩)
    ⟨by
      intro P Q h
      apply Subtype.ext
      exact primaryPrime_injective (hT P.val P.property) (hT Q.val Q.property) (congrArg Subtype.val h),by
      intro a
      obtain ⟨P,hP,he⟩ := Finset.mem_image.mp a.property
      exact ⟨⟨P,hP⟩,Subtype.ext he⟩⟩

@[simp] lemma canonicalSlotEquiv_val (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (P : T) : (canonicalSlotEquiv T hT P).val=primaryGenerator P.val.val := rfl

lemma canonicalSlotEquiv_span (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (P : T) : Ideal.span {(canonicalSlotEquiv T hT P).val}=P.val.val :=
  span_primaryGenerator_of_supported _ (hT P.val P.property)

lemma canonicalSlotEquiv_norm (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (P : T) : elementNorm (canonicalSlotEquiv T hT P).val=(Ideal.absNorm P.val.val:ℝ) :=
  primaryTuple_norm P.val (hT P.val P.property)

def canonicalTupleEquiv {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) :
    (∀i,↥(T i)) ≃ (∀i,↥(canonicalSlotSupport (T i))) :=
  Equiv.piCongrRight (fun i=>canonicalSlotEquiv (T i) (hT i))

@[simp] lemma canonicalTupleEquiv_val {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (P : ∀i,↥(T i)) (i : Fin K) :
    (canonicalTupleEquiv T hT P i).val=primaryGenerator (P i).val.val := rfl

theorem sum_canonical_element_tuples {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(canonicalSlotSupport (T i))),F (fun i=>(p i).val))=
      ∑P : (∀i,↥(T i)),F (fun i=>primaryGenerator (P i).val.val) := by
  exact ((canonicalTupleEquiv T hT).sum_comp (fun p=>F (fun i=>(p i).val))).symm

lemma canonicalSlotSupport_disjoint (T U : Finset PrimeIdeal)
    (hT : ∀P∈T,Supported P.val) (hU : ∀P∈U,Supported P.val) (hdis : Disjoint T U) :
    Disjoint (canonicalSlotSupport T) (canonicalSlotSupport U) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨P,hP,hPa⟩ := Finset.mem_image.mp ha
  obtain ⟨Q,hQ,hQa⟩ := Finset.mem_image.mp hb
  have he : P=Q := primaryPrime_injective (hT P hP) (hU Q hQ) (hPa.trans hQa.symm)
  exact Finset.disjoint_left.mp hdis hP (he.symm ▸ hQ)

lemma idealTuple_injective_of_disjoint {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j))) (P : ∀i,↥(T i)) :
    Function.Injective (fun i=>(P i).val) := by
  intro i j he
  by_contra hij
  apply Finset.disjoint_left.mp (hdis hij) (P i).property
  rw [show (P i).val=(P j).val from he]
  exact (P j).property

lemma canonicalElementTuple_injective_of_disjoint {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j))) (P : ∀i,↥(T i)) :
    Function.Injective (fun i=>primaryGenerator (P i).val.val) := by
  intro i j he
  apply idealTuple_injective_of_disjoint T hdis P
  exact primaryPrime_injective (hT i _ (P i).property) (hT j _ (P j).property) he

theorem sum_canonical_weighted_tuples {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(canonicalSlotSupport (T i))),
      (∏i,W i (elementNorm (p i).val/Y i))*F (fun i=>(p i).val))=
      ∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Y i))*
        F (fun i=>primaryGenerator (P i).val.val) := by
  rw [sum_canonical_element_tuples T hT (fun p=>(∏i,W i (elementNorm (p i)/Y i))*F p)]
  apply Finset.sum_congr rfl
  intro P hP
  simp only [primaryTuple_norm (P _).val (hT _ _ (P _).property)]

def idealSlotOfPrimary (A : Finset O) (hp : ∀a∈A,Prime (Ideal.span {a})) : Finset PrimeIdeal :=
  A.attach.image (fun a : A => (⟨Ideal.span {a.val}, hp a.val a.property⟩ : PrimeIdeal))

lemma idealSlotOfPrimary_supported (A : Finset O) (hp : ∀a∈A,Prime (Ideal.span {a}))
    (hs : ∀a∈A,Supported (Ideal.span {a})) :
    ∀P∈idealSlotOfPrimary A hp,Supported P.val := by
  intro P hP
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hP
  exact hs a.val a.property

lemma primarySlotNormalization (A : Finset O) (hp : ∀a∈A,Prime (Ideal.span {a}))
    (hs : ∀a∈A,Supported (Ideal.span {a}))
    (hprimary : ∀a∈A,ConcretePrimeRowBridge.goodLambda^2∣a-1) :
    canonicalSlotSupport (idealSlotOfPrimary A hp)=A := by
  have hg (a : A) : primaryGenerator (Ideal.span {a.val})=a.val := by
    apply primaryGenerator_span a.val
    · intro hz
      have hn := (hs a.val a.property).1
      exact hn (by simp [hz])
    · exact hprimary a.val a.property
  apply Finset.ext
  intro a
  constructor
  · intro ha
    obtain ⟨P,hP,hPa⟩ := Finset.mem_image.mp ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hP
    change primaryGenerator (Ideal.span {b.val})=a at hPa
    rw [hg b] at hPa
    exact hPa ▸ b.property
  · intro ha
    apply Finset.mem_image.mpr
    refine ⟨⟨Ideal.span {a},hp a ha⟩,?_,?_⟩
    · exact Finset.mem_image.mpr ⟨⟨a,ha⟩,by simp,rfl⟩
    · exact hg ⟨a,ha⟩

lemma canonicalSlotSupport_disjoint_iff (T U : Finset PrimeIdeal)
    (hT : ∀P∈T,Supported P.val) (hU : ∀P∈U,Supported P.val) :
    Disjoint (canonicalSlotSupport T) (canonicalSlotSupport U)↔Disjoint T U := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro P hP hQ
    exact Finset.disjoint_left.mp h (Finset.mem_image.mpr ⟨P,hP,rfl⟩)
      (Finset.mem_image.mpr ⟨P,hQ,rfl⟩)
  · exact canonicalSlotSupport_disjoint T U hT hU

lemma originalPrimarySlots_disjoint (A B : Finset O)
    (hAp : ∀a∈A,Prime (Ideal.span {a})) (hBp : ∀b∈B,Prime (Ideal.span {b}))
    (hAs : ∀a∈A,Supported (Ideal.span {a})) (hBs : ∀b∈B,Supported (Ideal.span {b}))
    (hAn : ∀a∈A,ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (hBn : ∀b∈B,ConcretePrimeRowBridge.goodLambda^2∣b-1) (h : Disjoint A B) :
    Disjoint (idealSlotOfPrimary A hAp) (idealSlotOfPrimary B hBp) := by
  apply (canonicalSlotSupport_disjoint_iff _ _
    (idealSlotOfPrimary_supported A hAp hAs) (idealSlotOfPrimary_supported B hBp hBs)).mp
  simpa only [primarySlotNormalization A hAp hAs hAn,primarySlotNormalization B hBp hBs hBn] using h

theorem sum_original_primary_weighted_tuples {K : ℕ} (A : Fin K→Finset O)
    (hp : ∀i a,a∈A i→Prime (Ideal.span {a}))
    (hs : ∀i a,a∈A i→Supported (Ideal.span {a}))
    (hn : ∀i a,a∈A i→ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(A i)),(∏i,W i (elementNorm (p i).val/Y i))*F (fun i=>(p i).val))=
      ∑P : (∀i,↥(idealSlotOfPrimary (A i) (hp i))),
        (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Y i))*F (fun i=>primaryGenerator (P i).val.val) := by
  have he (i : Fin K) := primarySlotNormalization (A i) (hp i) (hs i) (hn i)
  have hh := sum_canonical_weighted_tuples (fun i=>idealSlotOfPrimary (A i) (hp i))
    (fun i=>idealSlotOfPrimary_supported (A i) (hp i) (hs i)) W Y F
  let G (B : Fin K→Finset O) : ℂ :=
    ∑p : (∀i,↥(B i)),(∏i,W i (elementNorm (p i).val/Y i))*F (fun i=>(p i).val)
  have hfun : (fun i=>canonicalSlotSupport (idealSlotOfPrimary (A i) (hp i)))=A := funext he
  change G (fun i=>canonicalSlotSupport (idealSlotOfPrimary (A i) (hp i)))=_ at hh
  rw [hfun] at hh
  exact hh

end SevenEighths.ProbePhysical
end

end OAI

end Source1252

/- Original source: OAI/NumberTheory/DirichletL/Detector/CanonicalPhysicalRows.lean; sha256: 9e4cbee4b1c67854f46e254023def70567d4ae739469f767dd437fea734bca2e -/
section Source1253
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem compensatedPhysicalProbe_canonical_slots {K : ℕ} (η : HeckeFamily.Character)
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (X Y Z : ℝ) :
    compensatedPhysicalProbe η C W0 W1 (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      ∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        compensatedTuple η C W0 W1 (fun i=>primaryGenerator (P i).val.val) X Y Z :=
  sum_canonical_weighted_tuples T hT W Yp (fun p=>compensatedTuple η C W0 W1 p X Y Z)

theorem finitePhysicalRows_canonical_slots {K : ℕ} (S : Finset Id) (hmax : ∀P∈S,P.IsMaximal)
    (η : HeckeFamily.Character) (R : Finset FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    ProbeHighRowFamily.finitePhysicalRows S hmax η R T W Yp W0 W1 X Y Z=
      ∑p : (∀i,↥(canonicalSlotSupport (T i))),
        (∏i,W i (elementNorm (p i).val/Yp i))*
          ∑u∈R,rowIntegral η S (calibrationForSet S hmax) (fun i=>(p i).val) W0 W1 X Y Z u := by
  rw [sum_canonical_weighted_tuples T hT W Yp
    (fun p=>∑u∈R,rowIntegral η S (calibrationForSet S hmax) p W0 W1 X Y Z u)]
  unfold ProbeHighRowFamily.finitePhysicalRows
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem compensatedPhysicalProbe_eq_canonical_rows {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
      (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      ∑'u : FreeRow,∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u := by
  have hn (P : ∀i,↥(T i)) (i : Fin K) : primaryGenerator (P i).val.val≠0 :=
    supported_primaryGenerator_ne_zero _ (hT i _ (P i).property)
  have hs (P : ∀i,↥(T i)) : Summable (fun u : FreeRow=>
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) :=
    (rowIntegral_summable η S _ _ (hn P) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).mul_left _
  rw [compensatedPhysicalProbe_canonical_slots η _ W0 W1 T hT W Yp]
  calc
    _ = ∑P : (∀i,↥(T i)),∑'u : FreeRow,(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
      rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [compensatedTuple_eq_row_triple η S hS hpS hbad hSne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
          _ (hn P) X Y Z hX hY hZ,
          compensatedRowTripleIntegral_eq_tsum η S _ _ (hn P) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
        exact tsum_mul_left.symm
    _ = _ := (Summable.tsum_finsetSum (fun P _=>hs P)).symm

theorem finitePhysicalRows_original_primary_slots {K : ℕ} (S : Finset Id)
    (hmax : ∀P∈S,P.IsMaximal) (η : HeckeFamily.Character) (R : Finset FreeRow)
    (A : Fin K→Finset O) (hp : ∀i a,a∈A i→Prime (Ideal.span {a}))
    (hs : ∀i a,a∈A i→Supported (Ideal.span {a}))
    (hn : ∀i a,a∈A i→ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    ProbeHighRowFamily.finitePhysicalRows S hmax η R
      (fun i=>idealSlotOfPrimary (A i) (hp i)) W Yp W0 W1 X Y Z=
      ∑p : (∀i,↥(A i)),(∏i,W i (elementNorm (p i).val/Yp i))*
        ∑u∈R,rowIntegral η S (calibrationForSet S hmax) (fun i=>(p i).val) W0 W1 X Y Z u := by
  rw [sum_original_primary_weighted_tuples A hp hs hn W Yp
    (fun p=>∑u∈R,rowIntegral η S (calibrationForSet S hmax) p W0 W1 X Y Z u)]
  unfold ProbeHighRowFamily.finitePhysicalRows
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

end SevenEighths.ProbePhysical
end

end OAI

end Source1253

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/PhysicalPartition.lean; sha256: 25373eaeb09764d700f3df8664919446f24a10fc1a60e629547322b4049cf38f -/
section Source1254
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CompletedGauss CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

def physicalRowValue {K : ℕ} (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset PrimeIdeal) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (u : FreeRow) : ℂ :=
  ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
    rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u

theorem physicalRowValue_summable {K : ℕ} (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Summable (physicalRowValue S hmax η T W Yp W0 W1 X Y Z) := by
  have hs (P : ∀i,T i) : Summable (fun u : FreeRow=>
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) :=
    (rowIntegral_summable η S _ _ (fun i=>supported_primaryGenerator_ne_zero _ (hT i _ (P i).property))
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).mul_left _
  have hh (F : Finset (∀i,T i)) : Summable (fun u : FreeRow=>∑P∈F,
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert P F hP ih => simpa only [Finset.sum_insert hP] using (hs P).add ih
  exact hh Finset.univ

theorem canonical_physical_probe_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z L U : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (hL : 1≤L) (hLU : L≤U) :
    compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
      (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      (∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)+
      ((∑n∈smallDyadicIndices L,finitePhysicalRows S hmax η (smallDyadicRows L n) T W Yp W0 W1 X Y Z)+
        finitePhysicalRows S hmax η (rowBand L U) T W Yp W0 W1 X Y Z+
        (∑'n : ℕ,finitePhysicalRows S hmax η (dyadicRows U n) T W Yp W0 W1 X Y Z)) := by
  let f := physicalRowValue S hmax η T W Yp W0 W1 X Y Z
  have hf := physicalRowValue_summable S hmax η T hT W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [compensatedPhysicalProbe_eq_canonical_rows η S hmax hS.prime hS.bad ((by simp [fixedBadPrimes] : fixedBadPrimes.Nonempty).mono hS.bad) T hT W Yp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  change (∑'u,f u)=_
  rw [hf.tsum_eq_add_tsum_ite principalFreeRow]
  have heq : (fun u : FreeRow=>if u=principalFreeRow then 0 else f u)=
      (fun u : FreeRow=>if u.val=1 then 0 else f u) := by
    funext u
    have hu : u=principalFreeRow ↔ u.val=1 := by
      constructor
      · intro h;subst u;rfl
      · intro h;exact Subtype.ext h
    simp only [hu]
  rw [heq,nonprincipal_rows_partition L U hL hLU f hf]
  congr 1
  · dsimp [f,physicalRowValue]
    simp only [rowIntegral_principal]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1254

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/SmallSum.lean; sha256: 3d4e2508b16059f13f430eee8bab2cb20af6dc66defe764c018ecd0994178f2b -/
section Source1255
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily

lemma small_dyadic_square_sum : ∃C : ℝ,0<C ∧ ∀H : ℝ,0<H → ∀F : Finset ℕ,
    (∀n∈F,(2:ℝ)^n≤H) → (∑n∈F,((2:ℝ)^n)^(2:ℝ))≤C*H^(2:ℝ) := by
  obtain ⟨C,hC,hmain⟩ := CompletedDyadic.kernel_sum_bound 2 3 (by norm_num) (by norm_num)
  refine ⟨8*C,by positivity,?_⟩
  intro H hH F hF
  obtain ⟨hs,hb⟩ := hmain H⁻¹ (inv_pos.mpr hH)
  have hpoint (n : ℕ) (hn : n∈F) : ((2:ℝ)^n)^(2:ℝ)≤8*CompletedDyadic.kernelTerm H⁻¹ 2 3 n := by
    have hd : 0<1+H⁻¹*(2:ℝ)^n := by positivity
    have hu : H⁻¹*(2:ℝ)^n≤1 := by
      rw [mul_comm,←div_eq_mul_inv]
      exact (div_le_one hH).mpr (hF n hn)
    have hh : (1+H⁻¹*(2:ℝ)^n)^3≤(2:ℝ)^3 := pow_le_pow_left₀ hd.le (by linarith) 3
    unfold CompletedDyadic.kernelTerm
    norm_num only [Real.rpow_natCast,Real.rpow_ofNat]
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hd 3)).mpr
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ((2:ℝ)^n))
    norm_num at hm
    nlinarith only [hm]
  calc
    _ ≤ ∑n∈F,8*CompletedDyadic.kernelTerm H⁻¹ 2 3 n := Finset.sum_le_sum hpoint
    _ = 8*∑n∈F,CompletedDyadic.kernelTerm H⁻¹ 2 3 n := (Finset.mul_sum _ _ _).symm
    _ ≤ 8*∑'n,CompletedDyadic.kernelTerm H⁻¹ 2 3 n :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum F (fun n _=>by unfold CompletedDyadic.kernelTerm;positivity)) (by norm_num)
    _ ≤ 8*(C*(H⁻¹)^(-2:ℝ)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by rw [Real.inv_rpow hH.le,Real.rpow_neg hH.le,inv_inv];ring

end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source1255

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/SmallTail.lean; sha256: 98965e184ea007bfe1a3e36e544a2d783c005e61ba2989d7ea5110c190777c47 -/
section Source1256
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem small_physical_dyads_sum (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      (∑n∈F,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50))
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K e δ a b (17/50) B
    (HeckeZeroSupremum.beta+8*e) (1/2) he he' hδ (by linarith) ha hb le_rfl hB
    (by linarith) le_rfl le_rfl S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨D,hD,hsmall⟩ := small_dyadic_square_sum
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e)
  have hA : 0≤A := by dsimp [A];positivity
  have hbnd (n : ℕ) (hn : n∈F) :
      absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50)
      ≤A*((2:ℝ)^n)^(2:ℝ) := by
    have hUn : 1≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
    have hh := (hmain η ((2:ℝ)^n) hUn (R n) (hR n hn) T hT hdis (fun i=>Z^(length i)) hYp
      W hWS hWB (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
      (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
    have hpow : ((2:ℝ)^n)^(8/5+δ-(17/50:ℝ))≤((2:ℝ)^n)^(2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hUn (by linarith)
    have hscale := small_source_scale Z hZ0 length hl HeckeZeroSupremum.beta e
    calc
      _ ≤ (C*(η.modulus.absNorm:ℝ)^δ)*((2:ℝ)^n)^(8/5+δ-(17/50:ℝ))*
          Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e) := by
        apply hh.trans_eq
        rw [←hscale]
        ring
      _ ≤ (C*(η.modulus.absNorm:ℝ)^δ)*((2:ℝ)^n)^(2:ℝ)*
          Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e) := by gcongr
      _ = _ := by dsimp [A];ring
  calc
    _ ≤ ∑n∈F,A*((2:ℝ)^n)^(2:ℝ) := Finset.sum_le_sum hbnd
    _ = A*∑n∈F,((2:ℝ)^n)^(2:ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*(D*(Z^(1/100:ℝ))^(2:ℝ)) := mul_le_mul_of_nonneg_left
      (hsmall (Z^(1/100:ℝ)) (Real.rpow_pos_of_pos hZ0 _) F hF) hA
    _ = _ := by
      dsimp [A]
      rw [←Real.rpow_mul hZ0.le]
      have he : Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e)*Z^((1/100:ℝ)*2)=
          Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
        rw [←Real.rpow_add hZ0]
        congr 1
        ring
      calc
        _ = (C*D)*(η.modulus.absNorm:ℝ)^δ*
            (Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e)*Z^((1/100:ℝ)*2)) := by ring
        _ = _ := by rw [he]

end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source1256

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/PhysicalSmallTail.lean; sha256: 4dba13a1cc28578fb83cd28eaada5eb79f09088c2f88ef0232c73fef634ba8f2 -/
section Source1257
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem small_original_physical_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      (∑n∈F,‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := small_physical_dyads_sum K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hmain' := hmain η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let g : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50)
  have hbnd (n : ℕ) (hn : n∈F) :
      ‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤N*g n := norm_finitePhysicalRows_le_absolute
    e (HeckeZeroSupremum.beta+8*e) (1/2) (17/50) he he' (by linarith) le_rfl
    (by linarith [HeckeZeroSupremum.beta_le_one]) le_rfl (by norm_num) le_rfl
    S hS hmax hfirst η (R n) (fun u hu=>(hR n hn u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  calc
    _ ≤ ∑n∈F,N*g n := Finset.sum_le_sum hbnd
    _ = N*∑n∈F,g n := (Finset.mul_sum _ _ _).symm
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)) :=
      mul_le_mul_of_nonneg_left hmain' hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source1257

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CanonicalTails.lean; sha256: 3e3514944e4f06cb011fd73548f8d1ef63ae9ab6fc087298ccf5060dfdfc80a4 -/
section Source1258
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem canonical_small_original_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := small_original_physical_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  let L := Z^(1/100:ℝ)
  have hrows (n : ℕ) (hn : n∈smallDyadicIndices L) (u : FreeRow) (hu : u∈smallDyadicRows L n) :
      u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n := by
    have hh := mem_dyadicRows.mp (mem_smallDyadicRows.mp hu).1
    exact ⟨hh.1,by simpa only [one_mul,rowNorm] using hh.2.1,by simpa only [one_mul,rowNorm] using hh.2.2.le⟩
  have hbnd := hmain η Z hZ (smallDyadicIndices L) (fun n hn=>mem_smallDyadicIndices.mp hn)
    (smallDyadicRows L) hrows T hT hdis length hl0 hl W hWS hWB
  have heq := sum_small_dyadicRows L (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)
  change finitePhysicalRows S hmax η (rowBand 1 L) T W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z=
    ∑n∈smallDyadicIndices L,finitePhysicalRows S hmax η (smallDyadicRows L n) T W (fun i=>Z^(length i)) W0 W1
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z at heq
  rw [heq]
  exact (norm_sum_le _ _).trans hbnd

theorem canonical_large_original_tail (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>finitePhysicalRows S hmax η (dyadicRows (Z^((13/16:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (dyadicRows (Z^((13/16:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨C,hC,hmain⟩ := large_original_physical_tail K δ a b B ζ saving hδ hδ' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  apply hmain η Z hZ (dyadicRows (Z^((13/16:ℝ)+ζ))) _ T hT hdis length hl0 hl W hWS hWB
  intro n u hu
  have hh := mem_dyadicRows.mp hu
  exact ⟨hh.1,hh.2.1,hh.2.2.le⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1258

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CanonicalReduction.lean; sha256: 9648af7dc18efeb4ab569036e5fe50d76f7b85e72e71c41158ffb97d00fd7ed5 -/
section Source1259
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O

def principalPhysicalPool {K : ℕ} (η : Character) (S : Finset (Ideal O))
    (T : Fin K→Finset PrimeIdeal) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
    principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z

theorem canonical_probe_minus_central (K : ℕ) (e δ a b B ζ saving : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finitePhysicalRows S hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T W (fun i=>Z^(length i))
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤
        C*(η.modulus.absNorm:ℝ)^δ*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)) := by
  obtain ⟨Cs,hCs,hs⟩ := canonical_small_original_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cl,hCl,hl⟩ := canonical_large_original_tail K δ a b B ζ saving hδ (by linarith) hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cs+Cl,add_pos hCs hCl,?_⟩
  intro η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hdec := canonical_physical_probe_partition S hS hmax η T
    (fun i P hP=>outside_prime_supported S hS.bad P (hT i P hP)) W (fun i=>Z^(length i)) W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
    (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (Real.one_le_rpow hZ (by norm_num)) (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  have hs' := hs η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hl' := hl η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hsmall : (∑n∈smallDyadicIndices (Z^(1/100:ℝ)),finitePhysicalRows S hmax η (smallDyadicRows (Z^(1/100:ℝ)) n)
      T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)=
      finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z :=
    (sum_small_dyadicRows (Z^(1/100:ℝ)) (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)).symm
  rw [hsmall] at hdec
  rw [hdec]
  have heq : principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z=
      ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Z^(length i)))*
        principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z := rfl
  rw [←heq,add_sub_cancel_left]
  rw [show ∀a b c : ℂ,a+b+c-b=a+c from fun a b c=>by ring]
  apply (norm_add_le _ _).trans
  apply (add_le_add hs' ((norm_tsum_le_tsum_norm hl'.1.norm).trans hl'.2)).trans
  calc
    _ ≤ (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+
        (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by gcongr <;> linarith
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1259

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/FirstJoint.lean; sha256: 86c755e71c186b9064f457bcf613ecf95c284cfdff976fc58d373c1708248b71 -/
section Source1260
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_physicalRow_first_joint_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) :
    ∃C : ℝ,0≤C ∧ ∀x w z : ℂ,x.re=2 → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*L*Cn*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro x w z hx hw hz
  have hn' := hn w hw
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (1/4) S hS hfirst T η u x w z (by rw [hx];norm_num) hw hz
      (by rw [hx];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤L :=
    HeckeReciprocalBound.reciprocal_norm_le _ (by norm_num) (by rw [hx])
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by rw [hx];norm_num) hx.le hw hz (by rw [hx];linarith)
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*L)*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (mul_nonneg hL hL)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1260

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/DetectorZeros.lean; sha256: 054c1c7aef3663542351baa604b3ee1c1f67730e141189ee8e4660184f0b6d12 -/
section Source1261
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily

def detectorEntire (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue=1 then HeckeOrigin.poleRemoved χ s else HeckeOrigin.continued χ s

lemma detectorEntire_eq_nonprincipal (χ : Character) (hχ : χ.residue≠1) :
    detectorEntire χ=LFunction χ := by
  funext s
  simp only [detectorEntire,HeckeOrigin.continued,ite_eq_right hχ]

lemma detectorEntire_entire (χ : Character) : Differentiable ℂ (detectorEntire χ) := by
  by_cases hχ : χ.residue=1
  · have he : detectorEntire χ=HeckeOrigin.poleRemoved χ := by funext s;simp [detectorEntire,hχ]
    rw [he]
    exact HeckeOrigin.poleRemoved_entire χ
  · rw [detectorEntire_eq_nonprincipal χ hχ]
    exact LFunction_entire_nonprincipal χ hχ

lemma detectorEntire_zero_iff (χ : Character) {s : ℂ} (hs : 0<s.re) :
    detectorEntire χ s=0 ↔ LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1) := by
  have h0 : s≠0 := by intro h;simp [h] at hs
  by_cases hχ : χ.residue=1
  · simp only [detectorEntire,ite_eq_left hχ]
    by_cases h1 : s=1
    · subst s
      simp [HeckeOrigin.poleRemoved_one_ne_zero χ hχ,hχ]
    · rw [HeckeOrigin.poleRemoved_eq χ h0 h1]
      simp [mul_eq_zero,sub_ne_zero.mpr h1,h1]
  · rw [detectorEntire_eq_nonprincipal χ hχ]
    simp [hχ]

lemma detectorEntire_ne_zero_of_one_lt_re (χ : Character) {s : ℂ} (hs : 1<s.re) :
    detectorEntire χ s≠0 := by
  intro hz
  exact LFunction_ne_zero_of_one_lt_re χ hs ((detectorEntire_zero_iff χ (by linarith)).mp hz).1

def detectorZeros (χ : Character) (T : ℝ) : Set ℂ :=
  {s | s∈HeckeDetectorZeros.rectangle T ∧ LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1)}

lemma detectorZeros_finite (χ : Character) (T : ℝ) : (detectorZeros χ T).Finite := by
  have ha : AnalyticOnNhd ℂ (detectorEntire χ) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (detectorEntire_entire χ)
  have hc := ha.preimage_zero_mem_codiscreteWithin
    (detectorEntire_ne_zero_of_one_lt_re χ (by norm_num : 1<(2:ℂ).re))
    (Set.mem_univ (2:ℂ)) isConnected_univ
  have hf := (HeckeDetectorZeros.rectangle_compact T).finite_sdiff_of_mem_codiscreteWithin
    (codiscreteWithin_mono (Set.subset_univ (HeckeDetectorZeros.rectangle T)) hc)
  convert hf using 1
  ext s
  by_cases hs : s∈HeckeDetectorZeros.rectangle T
  · have hr : 0<s.re := by have h:=hs.1;linarith
    simp [detectorZeros,hs,detectorEntire_zero_iff χ hr]
  · simp [detectorZeros,hs]

def detectorZeroFinset (χ : Character) (T : ℝ) : Finset ℂ := (detectorZeros_finite χ T).toFinset

@[simp] lemma mem_detectorZeroFinset (χ : Character) (T : ℝ) (s : ℂ) :
    s∈detectorZeroFinset χ T ↔ (51/100:ℝ)≤s.re ∧ s.re≤1 ∧ |s.im|≤T ∧
      LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1) := by
  simp only [detectorZeroFinset,Set.Finite.mem_toFinset,detectorZeros,HeckeDetectorZeros.rectangle,Set.mem_ofPred_eq]
  tauto

variable {ι : Type*} [Fintype ι]

def detectorFamilyZeros (χ : ι→Character) (T : ℝ) : Finset (ι × ℂ) :=
  Finset.univ.biUnion (fun i=>(detectorZeroFinset (χ i) T).image (fun s=>(i,s)))

@[simp] lemma mem_detectorFamilyZeros (χ : ι→Character) (T : ℝ) (i : ι) (s : ℂ) :
    (i,s)∈detectorFamilyZeros χ T ↔ (51/100:ℝ)≤s.re ∧ s.re≤1 ∧ |s.im|≤T ∧
      LFunction (χ i) s=0 ∧ ¬((χ i).residue=1 ∧ s=1) := by
  simp [detectorFamilyZeros]

def detectorRealParts (χ : ι→Character) (T : ℝ) : Finset ℝ :=
  insert (51/100) ((detectorFamilyZeros χ T).image (fun p=>p.2.re))

lemma detectorRealParts_nonempty (χ : ι→Character) (T : ℝ) : (detectorRealParts χ T).Nonempty :=
  Finset.insert_nonempty _ _

def detectorMaximum (χ : ι→Character) (T : ℝ) : ℝ :=
  (detectorRealParts χ T).max' (detectorRealParts_nonempty χ T)

lemma detectorMaximum_mem (χ : ι→Character) (T : ℝ) : detectorMaximum χ T∈detectorRealParts χ T :=
  Finset.max'_mem _ _

lemma detectorMaximum_bounds (χ : ι→Character) (T : ℝ) :
    (51/100:ℝ)≤detectorMaximum χ T ∧ detectorMaximum χ T≤1 := by
  constructor
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · norm_num
    · obtain ⟨⟨i,s⟩,hs,rfl⟩ := Finset.mem_image.mp hx
      exact (mem_detectorFamilyZeros χ T i s |>.mp hs).2.1

lemma detector_zero_re_le_maximum (χ : ι→Character) (T : ℝ) (i : ι) {s : ℂ}
    (hs : (51/100:ℝ)≤s.re) (ht : |s.im|≤T) (hz : LFunction (χ i) s=0)
    (hpole : ¬((χ i).residue=1 ∧ s=1)) : s.re≤detectorMaximum χ T := by
  have hle : s.re≤1 := by
    by_contra hn
    exact LFunction_ne_zero_of_one_lt_re (χ i) (lt_of_not_ge hn) hz
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(i,s),(mem_detectorFamilyZeros χ T i s).mpr ⟨hs,hle,ht,hz,hpole⟩,rfl⟩)

lemma detectorMaximum_attained (χ : ι→Character) (T : ℝ)
    (hmax : (51/100:ℝ)<detectorMaximum χ T) :
    ∃i s,LFunction (χ i) s=0 ∧ ¬((χ i).residue=1 ∧ s=1) ∧
      |s.im|≤T ∧ s.re=detectorMaximum χ T := by
  have hm := detectorMaximum_mem χ T
  rcases Finset.mem_insert.mp hm with hm|hm
  · exact False.elim ((ne_of_gt hmax) hm)
  · obtain ⟨⟨i,s⟩,hs,heq⟩ := Finset.mem_image.mp hm
    have hz := (mem_detectorFamilyZeros χ T i s).mp hs
    exact ⟨i,s,hz.2.2.2.1,hz.2.2.2.2,hz.2.2.1,heq⟩

lemma detectorMaximum_mono (χ : ι→Character) {T T' : ℝ} (hT : T≤T') :
    detectorMaximum χ T≤detectorMaximum χ T' := by
  rcases lt_or_ge (51/100:ℝ) (detectorMaximum χ T) with hm|hm
  · obtain ⟨i,s,hz,hpole,ht,heq⟩ := detectorMaximum_attained χ T hm
    rw [←heq]
    exact detector_zero_re_le_maximum χ T' i (by rw [heq];exact hm.le) (ht.trans hT) hz hpole
  · exact hm.trans (detectorMaximum_bounds χ T').1

lemma detector_nonzero_above_maximum (χ : ι→Character) (T : ℝ) (i : ι) {s : ℂ}
    (hs : detectorMaximum χ T<s.re) (ht : |s.im|≤T)
    (hpole : ¬((χ i).residue=1 ∧ s=1)) : LFunction (χ i) s≠0 := by
  intro hz
  exact (not_lt_of_ge (detector_zero_re_le_maximum χ T i
    ((detectorMaximum_bounds χ T).1.trans hs.le) ht hz hpole)) hs

lemma detector_reciprocal_differentiableAt (χ : ι→Character) (T : ℝ) (i : ι) {s : ℂ}
    (hs : detectorMaximum χ T<s.re) (ht : |s.im|≤T) :
    DifferentiableAt ℂ (HeckeReciprocal.reciprocal (χ i)) s := by
  apply reciprocal_differentiableAt_of_nonzero (χ i) s
    (by intro h;have hb:=(detectorMaximum_bounds χ T).1;norm_num [h] at hs;linarith)
  exact detector_nonzero_above_maximum χ T i hs ht

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1261

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/DetectorBins.lean; sha256: 8e24c6ac8cdbb4156ad9b7b65d33fe59a0e7a89d4c578f2650dabe2d6cd7673a -/
section Source1262
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily
variable {ι : Type*} [Fintype ι]

lemma detector_nonzero_on_buffered_disk (χ : ι→Character)
    (T a e : ℝ) (i : ℕ) (hT : 2<T) (ha : (51/100:ℝ)≤a) (he : 0<e)
    (hmax : detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e)
    (j : ι) (t : ℝ) (ht : |t|≤(3*i+2:ℕ)*T)
    {s : ℂ} (hs : s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e))
    (hpole : ¬((χ j).residue=1 ∧ s=1)) : LFunction (χ j) s≠0 := by
  have hn : ‖s-((2:ℂ)+t*Complex.I)‖≤2-a-2*e := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2:ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (s-((2:ℂ)+t*Complex.I))
  norm_num at hr hi
  have hre : a+2*e≤s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  have him : |s.im|≤3*(i+1:ℕ)*T := by
    have ht' := abs_add_le (s.im-t) t
    rw [sub_add_cancel] at ht'
    push_cast at ht ⊢
    nlinarith [hi.trans hn]
  exact detector_nonzero_above_maximum χ _ j (hmax.trans_le hre) him hpole

lemma detectorEntire_nonzero_on_buffered_disk (χ : ι→Character)
    (T a e : ℝ) (i : ℕ) (hT : 2<T) (ha : (51/100:ℝ)≤a) (he : 0<e)
    (hmax : detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e)
    (j : ι) (t : ℝ) (ht : |t|≤(3*i+2:ℕ)*T)
    {s : ℂ} (hs : s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e)) :
    detectorEntire (χ j) s≠0 := by
  have hn : ‖s-((2:ℂ)+t*Complex.I)‖≤2-a-2*e := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2:ℂ)+t*Complex.I))
  norm_num at hr
  have hre : 0<s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  intro hz
  obtain ⟨hL,hpole⟩ := (detectorEntire_zero_iff (χ j) hre).mp hz
  exact detector_nonzero_on_buffered_disk χ T a e i hT ha he hmax j t ht hs hpole hL

lemma exists_detector_buffered_bin (χ : ι→Character)
    (T e : ℝ) (hT : 2<T) (he : 0<e) (n : ℕ) (hn : 0<n)
    (hwidth : (49/100:ℝ)≤n*e) :
    ∃ i k : ℕ, 1 ≤ i ∧ i ≤ n ∧
      let a : ℝ := 51/100+e*k
      a≤1 ∧ a≤detectorMaximum χ (3*i*T) ∧
      detectorMaximum χ (3*i*T)<a+e ∧
      detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e ∧
      (51/100<a → ∃j s,LFunction (χ j) s=0 ∧ ¬((χ j).residue=1 ∧ s=1) ∧
        a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*i*T) ∧
      (∀j t,|t|≤(3*i+2:ℕ)*T → ∀s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e),
        detectorEntire (χ j) s≠0) := by
  let M : ℕ→ℝ := fun j=>detectorMaximum χ (3*(j+1:ℕ)*T)
  obtain ⟨i,hk,k,hone,hlo,hhi,hnext⟩ := Detector.exists_buffered_bin M hn he
    (fun j _=>detectorMaximum_bounds χ _) hwidth
  refine ⟨i+1,k,by omega,by omega,hone,hlo,hhi,?_,?_,?_⟩
  · exact hnext
  · intro ha
    obtain ⟨j,s,hz,hpole,ht,hs⟩ := detectorMaximum_attained χ (3*(i+1:ℕ)*T) (lt_of_lt_of_le ha hlo)
    exact ⟨j,s,hz,hpole,by rw [hs];exact hlo,by rw [hs];exact hhi,ht⟩
  · intro j t ht s hs
    apply detectorEntire_nonzero_on_buffered_disk χ T (51/100+e*k) e (i+1) hT
      (by nlinarith [Nat.cast_nonneg (α:=ℝ) k]) he hnext j t ht hs

lemma detectorMaximum_eq_nonprincipal (χ : ι→Character) (hχ : ∀i,(χ i).residue≠1) (T : ℝ) :
    detectorMaximum χ T=HeckeDetectorZeros.zeroMaximum χ hχ T := by
  have hz (i : ι) : detectorZeroFinset (χ i) T=HeckeDetectorZeros.zeroFinset (χ i) (hχ i) T := by
    ext s
    simp [hχ i]
  have hr : detectorRealParts χ T=HeckeDetectorZeros.realParts χ hχ T := by
    simp only [detectorRealParts,HeckeDetectorZeros.realParts,detectorFamilyZeros,HeckeDetectorZeros.familyZeros,hz]
  unfold detectorMaximum HeckeDetectorZeros.zeroMaximum
  simp only [hr]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1262

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/DiskControl.lean; sha256: 925b34c4f797792b03e36d16a3cae1cc68f5ede1d7c1924ad7f8045c4bfcd52f -/
section Source1263
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic HeckeFiniteDeletion
open HeckeDeletionBounds HeckeReciprocalGrowth

lemma poleRemoved_eq_regularizedL (χ : Character) {s : ℂ} (hs : 0<s.re) :
    HeckeOrigin.poleRemoved χ s=HeckeReciprocal.regularizedL χ s := by
  by_cases h1 : s=1
  · subst s;exact HeckeOrigin.poleRemoved_one χ
  · have h0 : s≠0 := by intro h;simp [h] at hs
    rw [HeckeOrigin.poleRemoved_eq χ h0 h1,HeckeReciprocal.regularizedL_eq χ h0 h1]

lemma regular_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0<s.re) : regular χ s=regular ψ s*factors χ.modulus ψ s := by
  by_cases hχ : χ.residue=1
  · have hψ := (principal_iff_of_mask χ ψ hmask).mp hχ
    simp only [regular,ite_eq_left hχ,ite_eq_left hψ,HeckePrincipalStrip.sourceNormalized,
      poleRemoved_eq_regularizedL χ hs,poleRemoved_eq_regularizedL ψ hs]
    rw [regularizedL_eq_of_mask χ ψ hmask hs]
    ring
  · have hψ : ψ.residue≠1 := fun h=>hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
    rw [regular_eq_nonprincipal χ hχ,regular_eq_nonprincipal ψ hψ]
    exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs

lemma regular_eq_detector (χ : Character) (s : ℂ) :
    regular χ s=if χ.residue=1 then detectorEntire χ s/(s+1) else detectorEntire χ s := by
  by_cases hχ : χ.residue=1
  · simp [regular,detectorEntire,HeckePrincipalStrip.sourceNormalized,hχ]
  · simp [regular,detectorEntire_eq_nonprincipal χ hχ,hχ]

lemma regular_nonzero_of_detector (χ : Character) {s : ℂ} (hs : 0<s.re)
    (hz : detectorEntire χ s≠0) : regular χ s≠0 := by
  rw [regular_eq_detector]
  split_ifs
  · apply div_ne_zero hz
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
    linarith
  · exact hz

lemma reciprocal_norm_le_regular_inverse_on_positive (χ : Character) {s : ℂ}
    (hs : 0<s.re) (hz : regular χ s≠0) :
    ‖HeckeReciprocal.reciprocal χ s‖≤‖(regular χ s)⁻¹‖ := by
  have h0 : s≠0 := by intro h;simp [h] at hs
  by_cases hχ : χ.residue=1
  · by_cases h1 : s=1
    · subst s
      rw [HeckeReciprocal.reciprocal_principal_one χ hχ,norm_zero]
      exact norm_nonneg _
    have hp : s+1≠0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
      linarith
    have hL : LFunction χ s≠0 := by
      intro h
      apply hz
      simp [regular,hχ,HeckePrincipalStrip.sourceNormalized,HeckeOrigin.poleRemoved_eq χ h0 h1,h]
    have heq : HeckeReciprocal.reciprocal χ s=((s-1)/(s+1))*(regular χ s)⁻¹ := by
      rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
      simp only [regular,ite_eq_left hχ,HeckePrincipalStrip.sourceNormalized,HeckeOrigin.poleRemoved_eq χ h0 h1]
      field_simp
    rw [heq,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hp)).mpr (principal_regular_factor_bound hs.le)
  · simp only [HeckeReciprocal.reciprocal,regular,ite_eq_right hχ,le_refl]

theorem original_regular_disk_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character), ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular χ z‖ + ‖HeckeReciprocal.reciprocal χ z‖ ≤
          C*(presentationComplexity χ t)^ε := by
  obtain ⟨Dp,B,hDp,_,hprimitive⟩ := HeckeLogarithmicActual.disk_control e ε he he' hε
  obtain ⟨Cd,hCd,hdelete⟩ := factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Dp*Cd,mul_pos hDp hCd,?_⟩
  intro χ a t ha ha' hzero z hz
  obtain ⟨ψ,_,hp,hn,hmask⟩ := exists_primitive_character χ
  have hzeroψ : ∀ w ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular ψ w ≠ 0 := by
    intro w hw
    have hwp : 0 < w.re := by
      have hr := LogarithmicControl.disk_re_gt hw
      linarith
    intro hh
    apply hzero w hw
    rw [regular_eq_of_mask χ ψ hmask hwp, hh, zero_mul]
  have hbound := (hprimitive ψ hp a t ha ha' hzeroψ).1 z hz
  have hz2 : z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    closedBall_subset_ball (by linarith) hz
  have hzre : (1/2 : ℝ) ≤ z.re := by
    have hr := LogarithmicControl.disk_re_gt hz2
    linarith
  have hzpos : 0 < z.re := by linarith
  have hdel := hdelete χ.modulus ψ z hzre
  have hL : regular χ z = regular ψ z*factors χ.modulus ψ z :=
    regular_eq_of_mask χ ψ hmask hzpos
  have hR : HeckeReciprocal.reciprocal χ z =
      HeckeReciprocal.reciprocal ψ z*(factors χ.modulus ψ z)⁻¹ :=
    HeckeDeletionReciprocal.reciprocal_eq_of_mask χ ψ hmask hzpos
  have hrec := reciprocal_norm_le_regular_inverse_on_positive ψ hzpos (hzeroψ z hz2)
  have hdel1 : ‖factors χ.modulus ψ z‖ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg ((factors χ.modulus ψ z)⁻¹)]
  have hdel2 : ‖(factors χ.modulus ψ z)⁻¹‖ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg (factors χ.modulus ψ z)]
  have hQ : complexity ψ t ≤ complexity χ t := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 ≤ complexity ψ t := (Real.exp_pos 1).le.trans (complexity_ge_exp ψ t)
  have hr0 : 0 ≤ ((radical χ.modulus).absNorm : ℝ) := by positivity
  rw [hL,hR,norm_mul,norm_mul]
  calc
    _ ≤ (‖regular ψ z‖+‖(regular ψ z)⁻¹‖)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^ε) := by
      have h1 := mul_le_mul_of_nonneg_left hdel1 (norm_nonneg (regular ψ z))
      have h2 := mul_le_mul hrec hdel2 (norm_nonneg _) (norm_nonneg _)
      nlinarith
    _ ≤ (Dp*(complexity ψ t)^ε)*(Cd*((radical χ.modulus).absNorm : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = (Dp*Cd)*(((radical χ.modulus).absNorm : ℝ)*complexity ψ t)^ε := by
      rw [Real.mul_rpow hr0 hc0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr0 hc0) (mul_le_mul_of_nonneg_left hQ hr0) hε.le)
      (mul_pos hDp hCd).le

theorem buffered_regular_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
      (T a : ℝ) (i : ℕ),2<T → (51/100:ℝ)≤a → a≤1 →
      detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e →
      ∀j t,|t|≤(3*i+2:ℕ)*T →
      ∀z∈closedBall ((2:ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular (χ j) z‖+‖HeckeReciprocal.reciprocal (χ j) z‖≤
          C*(presentationComplexity (χ j) t)^ε := by
  obtain ⟨C,hC,hbound⟩ := original_regular_disk_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ T a i hT ha ha1 hmax j t ht z hz
  apply hbound (χ j) a t (by linarith) ha1 _ z hz
  intro w hw
  have hre : 0<w.re := by have h:=LogarithmicControl.disk_re_gt hw;linarith
  exact regular_nonzero_of_detector (χ j) hre
    (detectorEntire_nonzero_on_buffered_disk χ T a e i hT ha he hmax j t ht (ball_subset_closedBall hw))

theorem buffered_rectangle_reciprocal_bound (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
      (T a H : ℝ) (i : ℕ),2<T → (51/100:ℝ)≤a → a≤1 →
      H≤(3*i+2:ℕ)*T → detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e →
      ∀j z,a+16*e≤z.re → z.re≤2 → |z.im|≤H →
        ‖HeckeReciprocal.reciprocal (χ j) z‖≤C*(presentationComplexity (χ j) H)^ε := by
  obtain ⟨C,hC,hbound⟩ := buffered_regular_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ T a H i hT ha ha1 hHT hmax j z hzl hzr hzi
  have hz : z∈closedBall ((2:ℂ)+z.im*Complex.I) (2-a-6*e) := by
    rw [mem_closedBall,dist_eq_norm]
    have heq : z-((2:ℂ)+z.im*Complex.I)=((z.re-2:ℝ):ℂ) := by apply Complex.ext <;> simp
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    linarith
  have hb := hbound χ T a i hT ha ha1 hmax j z.im (hzi.trans hHT) z hz
  have hc : presentationComplexity (χ j) z.im≤presentationComplexity (χ j) H := by
    unfold presentationComplexity complexity
    have hH : 0≤H := (abs_nonneg _).trans hzi
    rw [abs_of_nonneg hH]
    gcongr
  have hnonneg : 0≤presentationComplexity (χ j) z.im := by
    unfold presentationComplexity complexity
    positivity
  apply (le_trans (le_add_of_nonneg_left (norm_nonneg _)) hb).trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hnonneg hc hε.le) hC.le

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1263

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/BufferedBin.lean; sha256: 12139ac3630fa9c4416b66d68a588838881d97158291f0550de3a7b80c9c7090 -/
section Source1264
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def sourceDetectorFamily (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) : Sum Bool ι→Character :=
  Sum.elim (fun b=>if b then rowCharacter S hS u else (targetRow η u).excludePrimes S hS) ψ

omit [Fintype ι] in
@[simp] lemma sourceDetectorFamily_denominator (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) :
    sourceDetectorFamily S hS η u ψ (Sum.inl false)=(targetRow η u).excludePrimes S hS := rfl

omit [Fintype ι] in
@[simp] lemma sourceDetectorFamily_numerator (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) :
    sourceDetectorFamily S hS η u ψ (Sum.inl true)=rowCharacter S hS u := rfl

lemma source_bin_denominator_nonzero (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) (T a e : ℝ) (i : ℕ) (he : 0<e)
    (hmax : detectorMaximum (sourceDetectorFamily S hS η u ψ) (3*(i+1:ℕ)*T)<a+2*e)
    (x : ℂ) (hx : a+16*e≤x.re) (ht : |x.im|≤3*(i+1:ℕ)*T)
    (hpole : ¬(((targetRow η u).excludePrimes S hS).residue=1 ∧ x=1)) :
    LFunction ((targetRow η u).excludePrimes S hS) x≠0 :=
  detector_nonzero_above_maximum (sourceDetectorFamily S hS η u ψ) _ (Sum.inl false)
    (by linarith) ht hpole

theorem source_buffered_x_rectangle {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmaxS : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow) (ψ : ι→Character)
    (T a e : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hfirst : FirstTail (4*e) S)
    (hmax : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*T)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z)
    (w z : ℂ) (hw : w.re=1-a-6*e) (hz : (17/50:ℝ)≤z.re)
    (r H : ℝ) (hr : a+16*e≤r) (hH : 0≤H) (hHT : H≤3*(i+1:ℕ)*T) :
    let F := fun x=>continuedPhysicalRowKernel S hS hmaxS P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -H..H,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -H..H,F ((((a+16*e):ℝ):ℂ)+t*I))+
        I*((∫v : ℝ in (a+16*e)..r,F ((v:ℂ)+(-H)*I))-
          (∫v : ℝ in (a+16*e)..r,F ((v:ℂ)+H*I))) := by
  apply buffered_x_rectangle (8*e) (by positivity) S hS
    (by convert hfirst using 1 ; ring) hmaxS P hPS η u W0 W1 X Y Z hZ w z (a+16*e) r H
    (by linarith) (by linarith) (by rw [hw];linarith) hz (by rw [hw];linarith) (by rw [hw];linarith)
  intro x hx hpole
  have hxr : a+16*e≤x.re := by simpa only [min_eq_left hr] using hx.1.1
  have hxi : |x.im|≤H := by
    apply abs_le.mpr
    simpa only [uIcc_of_le (by linarith : -H≤H),Set.mem_preimage,Set.mem_Icc] using hx.2
  exact source_bin_denominator_nonzero S hS.prime η u ψ T a e i he hmax x hxr (hxi.trans hHT) hpole

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1264

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/BufferedGrowth.lean; sha256: 08d2cc2f52e265fb04a97bbf0a84b8f361b92c131ec2f0c153932450a206e40f -/
section Source1265
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]

theorem calibrated_physicalRow_buffered_joint_growth
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e) :
    ∃C : ℝ,0≤C ∧ ∀x w z : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H → w.re=1-a-6*e → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let R : ℝ := Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^(1:ℝ)
  have hR : 0≤R := by
    dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
    positivity
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*R*Cn*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro x w z hxl hxr hxi hw hz
  have hwlow : -(1/100:ℝ)≤w.re := by rw [hw];linarith
  have hn' := hn w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz
      (by rw [hw];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤R :=
    hreciprocal (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
      (Sum.inl false) x hxl hxr hxi
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by linarith) hxr hwlow hz (by rw [hw];linarith)
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*R)*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (mul_nonneg hL hR)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1265

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/FirstIntegral.lean; sha256: 9158acbd0b2bb20acaa11f0150cc43768a2c6ca638d0010e3de4541f9696baa1 -/
section Source1266
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def rowAmplitudeOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1))*
    frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩*
    (star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u
        ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I))

lemma continuedRowOnLines_eq_amplitude {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) :
    continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r t=
      sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
        rowAmplitudeOnLines S hS hmax P hPS η u σ υ r t := by
  unfold continuedRowOnLines continuedPhysicalRowKernel rowAmplitudeOnLines
  ring

lemma rowAmplitudeOnLines_measurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (σ υ r : ℝ) : Measurable (rowAmplitudeOnLines S hS hmax P hPS η u σ υ r) := by
  have hp (i : Fin K) : 0<elementNorm (CompletedGauss.primaryGenerator (P i).val) :=
    elementNorm_pos _ (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
  have hN : (elementNorm u.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
  have hphys := physicalCompensatedRow_measurable S hS _ (contourTupleOutside S P hPS) η u
    (fun t : HeightSpace=>(σ:ℂ)+t.1.1*I) (fun t : HeightSpace=>(υ:ℂ)+t.2*I)
    (fun t : HeightSpace=>(r:ℂ)+t.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold rowAmplitudeOnLines
  apply Measurable.mul
  · apply Measurable.mul
    · apply Finset.measurable_prod
      intro i hi
      exact measurable_const_cpow _ (Complex.ofReal_ne_zero.mpr (hp i).ne') _ (by fun_prop)
    · unfold frequencyWeight
      exact measurable_const_cpow _ hN _ (by fun_prop)
  · exact hphys.const_mul _

lemma rowAmplitudeOnLines_first_bound {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (υ r : ℝ)
    (hυ : -(1/100:ℝ)≤υ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀t : HeightSpace,
      ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_joint_growth S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu
  let B : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hB : 0≤B := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨B*C,mul_nonneg hB hC,?_⟩
  intro t
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simp) (by simpa using hυ) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hB).trans_eq (by ring)

theorem continuedPhysicalRowKernel_first_integrable {K : ℕ}
    (υ r : ℝ) (hυ : -(1/100:ℝ)≤υ) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure := by
  obtain ⟨C,hC,hbound⟩ := rowAmplitudeOnLines_first_bound S hS hmax hfirst P hPS η u hu υ r hυ hr
  have hm := rowAmplitudeOnLines_measurable S hS hmax P hPS η u 2 υ r
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    2 2 r r υ υ (by linarith)
  have htwo (t : HeightSpace) : ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hbound t).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hh : 1≤(3+|t.1.1|)^2 := by nlinarith [abs_nonneg t.1.1]
    exact le_mul_of_one_le_right hC hh
  have hi := (hprofile 2 ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC _ hm.norm.aestronglyMeasurable (fun _=>norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ 2 r υ (by linarith)
  have hk : AEStronglyMeasurable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure := by
    have heq : continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r=
        (fun t=>sourceMellinWeight W0 W1 X Y Z ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
          rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t) := by funext t;exact continuedRowOnLines_eq_amplitude ..
    rw [heq]
    exact hs.aestronglyMeasurable.mul hm.aestronglyMeasurable
  exact hi.mono' hk (Filter.Eventually.of_forall fun t=>by rw [continuedRowOnLines_eq_amplitude,norm_mul])

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1266

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/BufferedIntegral.lean; sha256: 7ee530e8b7a02fd2515d73969d6a3c50e4c29ec247480b90b9357f63b4958756 -/
section Source1267
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma rowAmplitudeOnLines_buffered_bound {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (σ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀t : HeightSpace, |t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_joint_growth e a B H i he he' ha haTop hB hH S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ hbin
  let A : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hA : 0≤A := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro t ht
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ) (by simpa using hσ2) (by simpa using ht) (by simp) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)

theorem continuedPhysicalRowKernel_buffered_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤r) :
    IntegrableOn (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r)
      {t : HeightSpace | |t.1.1|≤H} heightMeasure := by
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  let A := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r)
  have hA : Measurable A := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).indicator hE
  obtain ⟨C,hC,hbound⟩ := rowAmplitudeOnLines_buffered_bound e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin σ r hσ hσ2 hr
  have hb (t : HeightSpace) : ‖A t‖≤C*(3+|t.2|)^2 := by
    by_cases ht : t∈E
    · simpa only [A,Set.indicator_of_mem ht] using hbound t ht
    · simp only [A,Set.indicator_of_notMem ht,norm_zero]
      positivity
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ r r (1-a-6*e) (1-a-6*e) (by linarith)
  have htwo (t : HeightSpace) : ‖A t‖≤C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hb t).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hh : 1≤(3+|t.1.1|)^2 := by nlinarith [abs_nonneg t.1.1]
    exact le_mul_of_one_le_right hC hh
  have hi := (hprofile σ ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e) ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC (fun t=>‖A t‖) hA.norm.aestronglyMeasurable (fun _=>norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ σ r (1-a-6*e) (by linarith)
  let F := fun t : HeightSpace => sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I)
      ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*A t
  have hm : AEStronglyMeasurable F heightMeasure := hs.aestronglyMeasurable.mul hA.aestronglyMeasurable
  have hf : Integrable F heightMeasure := hi.mono' hm (Filter.Eventually.of_forall fun t=>by dsimp [F];rw [norm_mul])
  have heq : E.indicator (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r)=F := by
    funext t
    by_cases ht : t∈E
    · simp only [Set.indicator_of_mem ht,F,A,continuedRowOnLines_eq_amplitude]
    · simp only [Set.indicator_of_notMem ht,F,A,mul_zero]
  exact (integrable_indicator_iff hE).mp (heq ▸ hf)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1267

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/FirstWShift.lean; sha256: 705c2f91d3dc5114acb4183a79b52d8523fe5fa753e1e9519c73d8a5792f2ddc -/
section Source1268
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma physicalRow_first_w_height_bound {K : ℕ} (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    ∃C : ℝ,0<C ∧ ∀v : ℝ,l≤v → ∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_w_growth (eps/2) S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu x z l hx hl hz (by linarith)
  refine ⟨9*C,by positivity,?_⟩
  intro v hv t
  have hb := hbound ((v:ℂ)+t*I) (by simpa using hv)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,mul_one,I_re,mul_zero,add_zero,zero_add] at hb
  apply hb.trans
  have h3 : (3+|t|)^2≤9*(height t)^2 := by unfold height;nlinarith [abs_nonneg t]
  nlinarith

theorem nonprincipal_first_w_integral_eq {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r : ℝ) (hlr : l≤r)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨C,hC,hbound⟩ := physicalRow_first_w_height_bound eps heps S hS hfirst hmax P hPS η u hu x z l hx hl hz hxw
  exact nonprincipal_w_integral_eq_of_polynomial eps heps S hS hfirst hmax P hPS η u hu
    W0 W1 a b ha hW X Y Z hY x z l r C 2 hC.le hlr hx hl hz hxw
    (fun v hv t=>hbound v hv.1 t)

lemma nonprincipal_first_w_vertical_integrable {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    Integrable (fun t : ℝ=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z) := by
  obtain ⟨C,hC,hbound⟩ := physicalRow_first_w_height_bound eps heps S hS hfirst hmax P hPS η u hu x z l hx hl hz hxw
  obtain ⟨B,hB,hb⟩ := continuedPhysicalRowKernel_cauchy S hS hmax P hPS η u W0 W1 a b ha hW X Y Z hY x z l l C 2 hC.le
    (fun v hv t=>hbound v hv.1 t)
  have hc : Continuous (fun t : ℝ=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (continuedPhysicalRowKernel_differentiableAt_w eps heps S hS hfirst hmax P hPS η u hu
      W0 W1 a b ha hW X Y Z hY x ((l:ℂ)+t*I) z hx (by simpa using hl) hz
      (by simpa using hxw)).continuousAt.comp (f:=fun t : ℝ=>(l:ℂ)+t*I)
    fun_prop
  exact (cauchy_integrable.const_mul B).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=>hb l ⟨le_rfl,le_rfl⟩ t))

theorem finite_rows_first_w_shift {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character)
    (F : Finset FreeRow) (hF : ∀u∈F,u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r : ℝ) (hlr : l≤r)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    (∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  rw [integral_finsetSum F (fun u hu=>nonprincipal_first_w_vertical_integrable eps heps S hS hfirst hmax P hPS η u (hF u hu)
    W0 W1 a b ha hW X Y Z hY x z l hx hl hz hxw),
    integral_finsetSum F (fun u hu=>nonprincipal_first_w_vertical_integrable eps heps S hS hfirst hmax P hPS η u (hF u hu)
      W0 W1 a b ha hW X Y Z hY x z r hx (hl.trans hlr) hz (by linarith))]
  exact Finset.sum_congr rfl (fun u hu=>nonprincipal_first_w_integral_eq eps heps S hS hfirst hmax P hPS η u (hF u hu)
    W0 W1 a b ha hW X Y Z hY x z l r hlr hx hl hz hxw)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1268

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/FirstTransport.lean; sha256: 06c5af27754d0faf5f10e3c5e7ed3590bd564f11aed17c715a16438454d3fdca -/
section Source1269
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma FirstTail.mono_parameter {eps eps' : ℝ} {S : Finset (Ideal O)}
    (h : FirstTail eps S) (hle : eps≤eps') : FirstTail eps' S := by
  have hp : 0<eps' := h.positive.trans_le hle
  refine ⟨hp,h.norm_four,?_⟩
  apply le_trans _ h.small
  apply ((firstPrimeDefectBound_summable eps' hp).subtype _).tsum_le_tsum _ h.summable
  intro P
  unfold firstPrimeDefectBound
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le
  · have hn := h.norm_four P.val P.property
    exact_mod_cast (by omega : 1≤P.val.val.absNorm)
  · have hm := min_le_min_right (1/50:ℝ) hle
    linarith

theorem continuedRowOnLines_first_w_transport {K : ℕ}
    (l r ξ : ℝ) (hl : -(1/100:ℝ)≤l) (hlr : l≤r) (hξ : (17/50:ℝ)≤ξ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 l ξ p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 r ξ p ∂heightMeasure := by
  have hi (q : ℝ) (hq : -(1/100:ℝ)≤q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 q ξ) heightMeasure :=
    continuedPhysicalRowKernel_first_integrable q ξ hq hξ S hS hmax hfirst P hPS η u hu W0 W1
      a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [integral_prod _ (hi l hl),integral_prod _ (hi r (hl.trans hlr))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  exact nonprincipal_first_w_integral_eq (1/2) (by norm_num) S hS (by norm_num;exact hfirst) hmax P hPS η u hu
    W0 W1 a1 b1 ha1 hW1 X Y Z hY ((2:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) l r hlr
    (by norm_num) hl (by simpa using hξ) (by norm_num;linarith)

theorem rowIntegral_first_w_lines {K : ℕ}
    (υ r : ℝ) (hυ : -(1/100:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p ∂heightMeasure := by
  have hβ : HeckeZeroSupremum.beta+8*(1/2000:ℝ)≤2 := by linarith [HeckeZeroSupremum.beta_le_one]
  obtain ⟨_,hphysical⟩ := rowIntegral_source_lines (1/2000) 2 3 r (by norm_num) (by norm_num)
    (by norm_num) hβ (by norm_num) (by norm_num) le_rfl hr S hS hmax hfirst P hP hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hw := continuedRowOnLines_first_w_transport υ 3 r hυ hυ3 hr S hS hmax hfirst P hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  exact ⟨continuedPhysicalRowKernel_first_integrable υ r hυ hr S hS hmax hfirst P hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ,hphysical.trans (by rw [hw])⟩

theorem rowIntegral_central_start {K : ℕ}
    (a e : ℝ) (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50)) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50) p ∂heightMeasure :=
  rowIntegral_first_w_lines (1-a-6*e) (17/50) (by linarith) (by linarith) le_rfl
    S hS hmax (hfirst.mono_parameter (by linarith)) P hP hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1269

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/BufferedTransport.lean; sha256: f48588d0f8ff619d64c39999d951bd794feb030cde62c3b55e8557acff7d23c5 -/
section Source1270
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma height_slab_integral_wzx (f : HeightSpace→ℂ) (H : ℝ) (hH : 0≤H)
    (hf : IntegrableOn f {t : HeightSpace | |t.1.1|≤H} heightMeasure) :
    (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H},f p ∂heightMeasure)=
      ∫w : ℝ,∫z : ℝ,∫x : ℝ in -H..H,f ((x,z),w) := by
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hi : Integrable (E.indicator f) heightMeasure := (integrable_indicator_iff hE).mpr hf
  rw [←integral_indicator hE,integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_left_ae] with w hw
  rw [integral_prod_symm _ hw]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have heq : (fun x : ℝ=>(E.indicator f) ((x,z),w))=(Icc (-H) H).indicator (fun x=>f ((x,z),w)) := by
    funext x
    simp only [Set.indicator_apply,E,Set.mem_ofPred_eq,Set.mem_Icc,abs_le]
  dsimp only
  rw [heq,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith)]

variable {ι : Type*} [Fintype ι]

theorem rowIntegral_buffered_transport {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH0 : 0≤H) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := fun x w z=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
    let E : Set HeightSpace := {t | |t.1.1|≤H}
    rowIntegral η S (calibrationForSet S hmax)
      (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ((∫tw : ℝ,∫tz : ℝ,
          (∫tx : ℝ in -H..H,F ((((a+16*e):ℝ):ℂ)+tx*I) ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I))+
          I*((∫v : ℝ in (a+16*e)..2,F ((v:ℂ)+(-H)*I) ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I))-
            (∫v : ℝ in (a+16*e)..2,F ((v:ℂ)+H*I) ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I))))+
          ∫p : HeightSpace in Eᶜ,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50) p ∂heightMeasure) := by
  dsimp only
  obtain ⟨hi,hrow⟩ := rowIntegral_central_start a e ha haTop he he' S hS hmax hfirst P hP hPS η u hu
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  rw [hrow,←integral_add_compl hE hi]
  congr 2
  rw [height_slab_integral_wzx _ H hH0 hi.integrableOn]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tw
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tz
  have hHT : H≤3*(i+1:ℕ)*B := by
    apply hH.trans
    have hn : (3*i+2:ℕ)≤3*(i+1) := by omega
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by linarith)
  simpa only [continuedRowOnLines,Complex.ofReal_div,Complex.ofReal_ofNat] using source_buffered_x_rectangle S hS hmax P hPS η u ψ B a e i he he' ha haTop hfirst hbin W0 W1 X Y Z hZ
    ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I) (by simp) (by norm_num) 2 H (by linarith) hH0 hHT

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1270

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/BufferedHeightGrowth.lean; sha256: d0e6128d19fad228d750c57f9b3641009aab0f57281fdacddc63f8331a17fbc3 -/
section Source1271
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]

theorem calibrated_physicalRow_buffered_height_growth
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    : ∃C : ℝ,0≤C ∧ ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H → w.re=1-a-6*e → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|H|)^2*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let R : ℝ := Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) 0)/9
  have hR : 0≤R := by
    dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
    positivity
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*R*Cn*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro a B H i ha ha1 hB hH hbin x w z hxl hxr hxi hw hz
  have hwlow : -(1/100:ℝ)≤w.re := by rw [hw];linarith
  have hn' := hn w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz
      (by rw [hw];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤R*(3+|H|)^2 := by
    have hr := hreciprocal (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
      (Sum.inl false) x hxl hxr hxi
    have hscale : Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^(1:ℝ)=R*(3+|H|)^2 := by
      dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
      rw [Real.rpow_one]
      ring
    simpa only [sourceDetectorFamily_denominator,hscale] using hr
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by linarith) hxr hwlow hz (by rw [hw];linarith)
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*(R*(3+|H|)^2))*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (by positivity)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1271

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/SliceIntegral.lean; sha256: f470226efefa32657d19c46e981f23025059c7b588c321fa36426b4376d1d592 -/
section Source1272
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical ProbeMellinBoundary

theorem source_profile_arithmetic_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃K : ℝ,0<K ∧ ∀σ∈Icc slo shi,∀ξ∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀axis : SliceAxis,∀T A : ℝ,0≤A → ∀X Y Z : ℝ,0<X → 0<Y → 0<Z →
      ∀G : ℝ×ℝ→ℂ,AEStronglyMeasurable G (volume.prod volume) →
      (∀q,‖G q‖≤A*jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J) →
      let F := fun q : ℝ×ℝ=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+(sliceMap axis T q).1.1*I) ((υ:ℂ)+(sliceMap axis T q).2*I)
        ((ξ:ℂ)+(sliceMap axis T q).1.2*I)*G q
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          A*K*(X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1))/height T^N := by
  obtain ⟨K,hK,hbound⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ axis T A hA X Y Z hX hY hZ G hG hGb
  let E : ℝ := X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1)
  have hE : 0≤E := by dsimp [E];positivity
  let S := fun q : ℝ×ℝ=>sourceScale X Y Z ((σ:ℂ)+(sliceMap axis T q).1.1*I)
    ((υ:ℂ)+(sliceMap axis T q).2*I) ((ξ:ℂ)+(sliceMap axis T q).1.2*I)
  have hc : Continuous (fun p : HeightSpace => (((σ:ℂ)+p.1.1*I,(υ:ℂ)+p.2*I),(ξ:ℂ)+p.1.2*I)) := by fun_prop
  have hS0 := (sourceScale_continuous X Y Z hX hY hZ).comp (hc.comp (sliceMap_continuous axis T))
  have hS : Continuous S := by simpa only [S,Function.comp_def] using hS0
  have hSn (q : ℝ×ℝ) : ‖S q‖=E := by
    dsimp only [S]
    rw [sourceScale_norm X Y Z hX hY hZ]
    simp [E]
  have hb (q : ℝ×ℝ) : ‖S q*G q‖≤(E*A)*jointHeight
      (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J := by
    rw [norm_mul,hSn]
    exact (mul_le_mul_of_nonneg_left (hGb q) hE).trans_eq (by ring)
  obtain ⟨hi,hb⟩ := hbound σ hσ ξ hξ υ hυ axis T (E*A) (mul_nonneg hE hA)
    (fun q=>S q*G q) (hS.aestronglyMeasurable.mul hG) hb
  have heq : (fun q : ℝ×ℝ=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+(sliceMap axis T q).1.1*I) ((υ:ℂ)+(sliceMap axis T q).2*I)
        ((ξ:ℂ)+(sliceMap axis T q).1.2*I)*G q)=
      (fun q=>(S q*G q)*onLines W0 W1 σ ξ υ (sliceMap axis T q)) := by
    funext q
    rw [sourceMellinWeight_eq_scale]
    dsimp [S,onLines]
    ring
  dsimp only
  refine ⟨heq.symm ▸ hi,?_⟩
  have hnorm := congrArg (fun f : ℝ×ℝ→ℂ => ∫q : ℝ×ℝ,‖f q‖ ∂volume.prod volume) heq
  rw [hnorm]
  calc
    _ ≤ (E*A)*K/height T^N := hb
    _ = _ := by dsimp [E];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1272

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/BufferedSlices.lean; sha256: 0d8e316c5258a86ca5a38a8b30aabe94cdeb0487f670f81f2e1502b6cc59ed6e -/
section Source1273
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma rowAmplitudeOnLines_buffered_uniform {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀σ∈Icc (a+16*e) 2,∀t : HeightSpace, |t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_joint_growth e a B H i he he' ha haTop hB hH S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ hbin
  let A : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hA : 0≤A := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro σ hσ t ht
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ.1) (by simpa using hσ.2) (by simpa using ht) (by simp) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)

theorem continuedPhysicalRowKernel_buffered_slices {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (N : ℕ)
    (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀σ∈Icc (a+16*e) 2,∀tx : ℝ,|tx|≤H →
      let F := fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height tx^N := by
  obtain ⟨A,hA,hrow⟩ := rowAmplitudeOnLines_buffered_uniform e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin r hr
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (a+16*e) 2 r r (1-a-6*e) (1-a-6*e) (by linarith) 2 N
  refine ⟨(9*A)*D,by positivity,?_⟩
  intro σ hσ tx htx
  let G := fun q : ℝ×ℝ=>rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r ((tx,q.1),q.2)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).comp (by fun_prop)
  have hb (q : ℝ×ℝ) : ‖G q‖≤(9*A)*jointHeight tx q.1 q.2^2 := by
    have hh : 3+|q.2|≤3*jointHeight tx q.1 q.2 := by
      unfold jointHeight
      linarith [abs_nonneg tx,abs_nonneg q.1,abs_nonneg q.2]
    apply (hrow σ hσ ((tx,q.1),q.2) htx).trans
    calc
      _ ≤ A*(3*jointHeight tx q.1 q.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) hA
      _ = _ := by ring
  have ht := hprofile σ hσ r ⟨le_rfl,le_rfl⟩ (1-a-6*e) ⟨le_rfl,le_rfl⟩ .s tx
    (9*A) (by positivity) X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  simpa only [sliceMap,G,continuedRowOnLines_eq_amplitude] using ht

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1273

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/BufferedJoinDecay.lean; sha256: 5256ce12dd9e33c753b2fb14afe92f80d753d4f761e6fe19d40b236034a04688 -/
section Source1274
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma rowAmplitudeOnLines_buffered_height_uniform {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀t : HeightSpace, |t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤C*(3+|H|)^2*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_height_growth e he he' S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ
  let A : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hA : 0≤A := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro a B H i ha haTop hB hH hbin σ hσ t ht
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound a B H i ha haTop hB hH hbin ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ.1) (by simpa using hσ.2) (by simpa using ht) (by simp) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)

theorem buffered_x_slice_arbitrary_decay {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ)
    (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A,hA,hrow⟩ := rowAmplitudeOnLines_buffered_height_uniform e he he' S hS hmax hfirst P hPS η u hu ψ r hr
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (51/100) 2 r r (-(1/100)) (1/2) (by linarith) 2 (N+2)
  refine ⟨81*A*D,by positivity,?_⟩
  intro X Y Z hX hY hZ a B H i ha haTop hB hH hbin σ hσ tx htx
  let G := fun q : ℝ×ℝ=>rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r ((tx,q.1),q.2)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).comp (by fun_prop)
  have hb (q : ℝ×ℝ) : ‖G q‖≤(9*A*(3+|H|)^2)*jointHeight tx q.1 q.2^2 := by
    have hh : 3+|q.2|≤3*jointHeight tx q.1 q.2 := by
      unfold jointHeight
      linarith [abs_nonneg tx,abs_nonneg q.1,abs_nonneg q.2]
    apply (hrow a B H i ha haTop hB hH hbin σ hσ ((tx,q.1),q.2) htx.le).trans
    calc
      _ ≤ (A*(3+|H|)^2)*(3*jointHeight tx q.1 q.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) (by positivity)
      _ = _ := by ring
  have ht := hprofile σ ⟨by linarith [hσ.1],hσ.2⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e)
    ⟨by linarith,by linarith⟩ .s tx (9*A*(3+|H|)^2) (by positivity)
    X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤
        (9*A*(3+|H|)^2)*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height tx^(N+2) := by
    simpa only [sliceMap,G,continuedRowOnLines_eq_amplitude] using ht
  refine ⟨ht'.1,ht'.2.trans ?_⟩
  have hH0 : 0≤H := htx ▸ abs_nonneg tx
  have hheight : height tx=height H := by simp [height,htx,abs_of_nonneg hH0]
  have hpow : (3+|H|)^2≤9*(height H)^2 := by
    have hh : 3+|H|≤3*height H := by unfold height;linarith [abs_nonneg H]
    have hh' := pow_le_pow_left₀ (by positivity) hh 2
    norm_num [mul_pow] at hh'
    exact hh'
  have hden : 0<height H := height_pos H
  rw [hheight]
  calc
    _ ≤ (9*A*(9*(height H)^2))*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^(N+2) := by
      gcongr
    _ = _ := by rw [pow_add];field_simp;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1274

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/HorizontalIntegral.lean; sha256: 1731faa68cdd5e2d34d9ee9089c75760993a86b8379da53eff46ddc805b13641 -/
section Source1275
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma continuedRow_horizontal_measurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (tx υ r : ℝ) (hr : 0<r) :
    Measurable (fun p : ℝ × (ℝ × ℝ)=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
      p.1 υ r ((tx,p.2.1),p.2.2)) := by
  have hR : Continuous (fun t : ℝ=>mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) ((r:ℂ)+t*I)) :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.comp_continuous
      (by fun_prop) (by intro t;simpa using hr)
  have hW := (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)).continuous
  have hcoords : Continuous (fun p : ℝ × (ℝ × ℝ)=>(((p.1:ℂ)+tx*I,(υ:ℂ)+p.2.2*I),(r:ℂ)+p.2.1*I)) := by fun_prop
  have hscale := (sourceScale_continuous X Y Z hX hY hZ).comp hcoords
  have hprof : Measurable (fun p : ℝ × (ℝ × ℝ)=>profile W0 W1
      ((p.1:ℂ)+tx*I) ((υ:ℂ)+p.2.2*I) ((r:ℂ)+p.2.1*I)) := by
    unfold profile
    apply Measurable.mul
    · apply Measurable.mul
      · fun_prop
      · exact hR.measurable.comp (by fun_prop)
    · exact hW.measurable.comp (by fun_prop)
  have hsource : Measurable (fun p : ℝ × (ℝ × ℝ)=>sourceMellinWeight W0 W1 X Y Z
      ((p.1:ℂ)+tx*I) ((υ:ℂ)+p.2.2*I) ((r:ℂ)+p.2.1*I)) := by
    simp_rw [sourceMellinWeight_eq_scale]
    exact hscale.measurable.mul hprof
  have hphysical := physicalCompensatedRow_measurable S hS _ (contourTupleOutside S P hPS) η u
    (fun p : ℝ × (ℝ × ℝ)=>(p.1:ℂ)+tx*I) (fun p : ℝ × (ℝ × ℝ)=>(υ:ℂ)+p.2.2*I)
    (fun p : ℝ × (ℝ × ℝ)=>(r:ℂ)+p.2.1*I) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold continuedRowOnLines continuedPhysicalRowKernel
  apply Measurable.mul
  · apply Measurable.mul
    · apply Measurable.mul hsource
      apply Finset.measurable_prod
      intro i hi
      apply measurable_const_cpow
      · exact Complex.ofReal_ne_zero.mpr (elementNorm_pos _
          (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero).ne'
      · fun_prop
    · unfold frequencyWeight
      apply measurable_const_cpow
      · exact Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
      · fun_prop
  · exact hphysical.const_mul _

lemma horizontal_integral_bound (F : ℝ→(ℝ×ℝ)→ℂ) (l r C : ℝ) (hlr : l≤r) (_hC : 0≤C)
    (hm : Measurable (Function.uncurry F))
    (hi : ∀v∈Ioc l r,Integrable (F v) (volume.prod volume))
    (hb : ∀v∈Ioc l r,(∫q : ℝ×ℝ,‖F v q‖ ∂volume.prod volume)≤C) :
    Integrable (fun q : ℝ×ℝ=>∫v : ℝ in l..r,F v q) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖∫v : ℝ in l..r,F v q‖ ∂volume.prod volume)≤(r-l)*C := by
  let μ : Measure ℝ := volume.restrict (Ioc l r)
  let ν : Measure (ℝ×ℝ) := volume.prod volume
  have hm' : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) := hm.aestronglyMeasurable
  have hnorm : Integrable (fun v=>∫q,‖F v q‖ ∂ν) μ := by
    apply (integrable_const C).mono' hm'.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _=>norm_nonneg _))]
    exact hb v hv
  have hprod : Integrable (Function.uncurry F) (μ.prod ν) := by
    apply (integrable_prod_iff hm').mpr
    refine ⟨?_,hnorm⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact hi v hv
  have hj : Integrable (fun q=>∫v,F v q ∂μ) ν := hprod.integral_prod_right
  simp only [intervalIntegral.integral_of_le hlr]
  refine ⟨hj,?_⟩
  calc
    _ ≤ ∫q,∫v,‖F v q‖ ∂μ ∂ν := integral_mono hj.norm hprod.integral_norm_prod_right
      (fun q=>norm_integral_le_integral_norm _)
    _ = ∫v,∫q,‖F v q‖ ∂ν ∂μ := integral_integral_swap hprod.norm.swap
    _ ≤ ∫v,C ∂μ := integral_mono_ae hnorm (integrable_const C) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      exact hb v hv)
    _ = _ := by
      dsimp [μ]
      rw [setIntegral_const,Real.volume_real_Ioc_of_le hlr,smul_eq_mul]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1275

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/BufferedJoins.lean; sha256: 17a0e9d2ecbf584a957dc4babbf82f18a0aa4a257bd7eab7d599ec30c4e04b54 -/
section Source1276
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem buffered_horizontal_join_arbitrary_decay {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>∫v : ℝ in (a+16*e)..2,
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound⟩ := buffered_x_slice_arbitrary_decay e he he' S hS hmax hfirst P hPS η u hu ψ
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N r hr
  refine ⟨2*C,by positivity,?_⟩
  intro X Y Z hX hY hZ a B H i ha haTop hB hH hbin tx htx
  let A : ℝ := C*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N
  have hA : 0≤A := by dsimp [A];exact div_nonneg (mul_nonneg hC (by unfold scaleBound;positivity)) (pow_nonneg (height_pos _).le _)
  have hslice (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :=
    hbound X Y Z hX hY hZ a B H i ha haTop hB hH hbin v ⟨hv.1.le,hv.2⟩ tx htx
  have hnorm (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        v (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤A := by
    apply (hslice v hv).2.trans
    have hz := rpow_le_scaleBound hZ
      (show v+r-1∈Icc ((51/100)+r-1) (2+r-1) by constructor <;> linarith [hv.1,hv.2])
    dsimp [A]
    gcongr
    exact pow_nonneg (height_pos H).le N
  have hm := continuedRow_horizontal_measurable S hS hmax P hPS η u W0 W1 a1 b1 ha1 hW1
    X Y Z hX hY hZ tx (1-a-6*e) r (by linarith)
  obtain ⟨hi,hb⟩ := horizontal_integral_bound
    (fun v q=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2))
    (a+16*e) 2 A (by linarith) hA hm (fun v hv=>(hslice v hv).1) hnorm
  refine ⟨hi,hb.trans ?_⟩
  calc
    _ ≤ 2*A := mul_le_mul_of_nonneg_right (by linarith : 2-(a+16*e)≤2) hA
    _ = _ := by dsimp [A];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1276

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/TailIntegral.lean; sha256: 9b807d2fa4e12716d6439f75d3bba2c0720a1bb9df430311b968619a9a48ab15 -/
section Source1277
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical ProbeMellinBoundary

theorem source_profile_arithmetic_tails (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃K : ℝ,0<K ∧ ∀σ∈Icc slo shi,∀ξ∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀A : ℝ,0≤A → ∀X Y Z : ℝ,0<X → 0<Y → 0<Z →
      ∀G : HeightSpace→ℂ,AEStronglyMeasurable G heightMeasure →
      (∀q,‖G q‖≤A*jointHeight q.1.1 q.1.2 q.2^J) →
      let F := fun q : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+q.1.1*I) ((υ:ℂ)+q.2*I)
        ((ξ:ℂ)+q.1.2*I)*G q
      Integrable F heightMeasure ∧ ∀T : ℝ,0≤T →
        (∫q : HeightSpace in outsideBox T,‖F q‖ ∂heightMeasure)≤
          A*K*(X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1))/(1+T)^N := by
  obtain ⟨K,hK,hbound⟩ := profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ A hA X Y Z hX hY hZ G hG hGb
  let E : ℝ := X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1)
  have hE : 0≤E := by dsimp [E];positivity
  let S := fun q : HeightSpace=>sourceScale X Y Z ((σ:ℂ)+q.1.1*I)
    ((υ:ℂ)+q.2*I) ((ξ:ℂ)+q.1.2*I)
  have hc : Continuous (fun p : HeightSpace => (((σ:ℂ)+p.1.1*I,(υ:ℂ)+p.2*I),(ξ:ℂ)+p.1.2*I)) := by fun_prop
  have hS0 := (sourceScale_continuous X Y Z hX hY hZ).comp hc
  have hS : Continuous S := by simpa only [S,Function.comp_def] using hS0
  have hSn (q : HeightSpace) : ‖S q‖=E := by
    dsimp only [S]
    rw [sourceScale_norm X Y Z hX hY hZ]
    simp [E]
  have hb (q : HeightSpace) : ‖S q*G q‖≤(E*A)*jointHeight
      q.1.1 q.1.2 q.2^J := by
    rw [norm_mul,hSn]
    exact (mul_le_mul_of_nonneg_left (hGb q) hE).trans_eq (by ring)
  obtain ⟨hi,hb⟩ := hbound σ hσ ξ hξ υ hυ (E*A) (mul_nonneg hE hA)
    (fun q=>S q*G q) (hS.aestronglyMeasurable.mul hG) hb
  have heq : (fun q : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+q.1.1*I) ((υ:ℂ)+q.2*I)
        ((ξ:ℂ)+q.1.2*I)*G q)=
      (fun q=>(S q*G q)*onLines W0 W1 σ ξ υ q) := by
    funext q
    rw [sourceMellinWeight_eq_scale]
    dsimp [S,onLines]
    ring
  dsimp only
  refine ⟨heq.symm ▸ hi,?_⟩
  intro T hT
  have hnorm := congrArg (fun f : HeightSpace→ℂ => ∫q : HeightSpace in outsideBox T,‖f q‖ ∂heightMeasure) heq
  rw [hnorm]
  calc
    _ ≤ (E*A)*K/(1+T)^N := hb T hT
    _ = _ := by dsimp [E];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1277

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/OriginalHeightTail.lean; sha256: 618373b88f7c8a9580a063a1b1ca77255a207f267bc360b564110433a1529125 -/
section Source1278
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma rowAmplitudeOnLines_first_uniform {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀υ : ℝ,-(1/100:ℝ)≤υ → ∀t : HeightSpace,
      ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_joint_growth S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu
  let B : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hB : 0≤B := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨B*C,mul_nonneg hB hC,?_⟩
  intro υ hυ t
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simp) (by simpa using hυ) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hB).trans_eq (by ring)

theorem original_x_height_tail {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀υ∈Icc (-(1/100:ℝ)) (1/2),∀X Y Z : ℝ,0<X → 0<Y → 0<Z →
      ∀H : ℝ,0≤H →
      (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H}ᶜ,
        ‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p‖ ∂heightMeasure)≤
        C*(X^(1/2-r)*Z^(2+r-1)*Y^(υ-1))/(1+H)^N := by
  obtain ⟨A,hA,hrow⟩ := rowAmplitudeOnLines_first_uniform S hS hmax hfirst P hPS η u hu r hr
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    2 2 r r (-(1/100)) (1/2) (by linarith) 2 N
  refine ⟨9*A*D,by positivity,?_⟩
  intro υ hυ X Y Z hX hY hZ H hH
  let G := rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r
  have hG : Measurable G := rowAmplitudeOnLines_measurable S hS hmax P hPS η u 2 υ r
  have hb (t : HeightSpace) : ‖G t‖≤(9*A)*jointHeight t.1.1 t.1.2 t.2^2 := by
    have hh : 3+|t.2|≤3*jointHeight t.1.1 t.1.2 t.2 := by
      unfold jointHeight
      linarith [abs_nonneg t.1.1,abs_nonneg t.1.2,abs_nonneg t.2]
    apply (hrow υ hυ.1 t).trans
    calc
      _ ≤ A*(3*jointHeight t.1.1 t.1.2 t.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) hA
      _ = _ := by ring
  have ht := hprofile 2 ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ hυ
    (9*A) (by positivity) X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure ∧
      ∀T : ℝ,0≤T →
      (∫p : HeightSpace in outsideBox T,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p‖ ∂heightMeasure)≤
        (9*A)*D*(X^(1/2-r)*Z^(2+r-1)*Y^(υ-1))/(1+T)^N := by
    have hfun : continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r=
        (fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z ((2:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((r:ℂ)+p.1.2*I)*G p) := by
      funext p
      exact continuedRowOnLines_eq_amplitude ..
    rw [hfun]
    exact ht
  apply le_trans _ (ht'.2 H hH)
  apply setIntegral_mono_set ht'.1.norm.integrableOn (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
  apply Filter.Eventually.of_forall
  intro p hp
  have hx : H < |p.1.1| := by simpa using hp
  exact Or.inl hx

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1278

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CentralIntegral.lean; sha256: 7ac09e9a557e9ffffbb6c9028de49f0b04ce6856d6aa07668570dd4e0487596f -/
section Source1279
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma height_slab_partial_integrable (f : HeightSpace→ℂ) (H : ℝ) (hH : 0≤H)
    (hf : IntegrableOn f {t : HeightSpace | |t.1.1|≤H} heightMeasure) :
    Integrable (fun q : ℝ×ℝ=>∫x : ℝ in -H..H,f ((x,q.1),q.2)) (volume.prod volume) := by
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hi : Integrable (E.indicator f) heightMeasure := (integrable_indicator_iff hE).mpr hf
  have hp := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ) (volume : Measure ℝ)).symm MeasurableEquiv.prodAssoc
  have hr : Integrable (fun p : ℝ × (ℝ × ℝ)=>(E.indicator f) ((p.1,p.2.1),p.2.2))
      (volume.prod (volume.prod volume)) := hp.integrable_comp_of_integrable hi
  have hj := hr.integral_prod_right
  have heq : (fun q : ℝ×ℝ=>∫x : ℝ,(E.indicator f) ((x,q.1),q.2))=
      (fun q : ℝ×ℝ=>∫x : ℝ in -H..H,f ((x,q.1),q.2)) := by
    funext q
    have hfun : (fun x : ℝ=>(E.indicator f) ((x,q.1),q.2))=
        (Icc (-H) H).indicator (fun x=>f ((x,q.1),q.2)) := by
      funext x
      simp only [Set.indicator_apply,E,Set.mem_ofPred_eq,Set.mem_Icc,abs_le]
    rw [hfun,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by linarith)]
  exact heq ▸ hj

lemma height_slab_integral_pair (f : HeightSpace→ℂ) (H : ℝ) (hH : 0≤H)
    (hf : IntegrableOn f {t : HeightSpace | |t.1.1|≤H} heightMeasure) :
    (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H},f p ∂heightMeasure)=
      ∫q : ℝ×ℝ,(∫x : ℝ in -H..H,f ((x,q.1),q.2)) ∂volume.prod volume := by
  rw [height_slab_integral_wzx f H hH hf]
  exact (integral_prod_symm _ (height_slab_partial_integrable f H hH hf)).symm

variable {ι : Type*} [Fintype ι]

theorem rowIntegral_central_decomposition {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH0 : 0≤H) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
    let E : Set HeightSpace := {t | |t.1.1|≤H}
    IntegrableOn (k (a+16*e)) E heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ((∫p : HeightSpace in E,k (a+16*e) p ∂heightMeasure)+
          I*((∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((-H,q.1),q.2)) ∂volume.prod volume)-
            (∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((H,q.1),q.2)) ∂volume.prod volume))+
          ∫p : HeightSpace in Eᶜ,k 2 p ∂heightMeasure) := by
  dsimp only
  let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  obtain ⟨hi,hrow⟩ := rowIntegral_central_start a e ha haTop he he' S hS hmax hfirst P hP hPS η u hu
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hleft := continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  obtain ⟨C,hC,hjoins⟩ := buffered_horizontal_join_arbitrary_decay e he he' S hS hmax hfirst P hPS η u hu ψ
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 0 (17/50) le_rfl
  have hJ (tx : ℝ) (htx : |tx|=H) :
      Integrable (fun q : ℝ×ℝ=>∫v : ℝ in (a+16*e)..2,k v ((tx,q.1),q.2)) (volume.prod volume) :=
    (hjoins X Y Z hX hY hZ a B H i ha haTop hB hH hbin tx htx).1
  have hm := hJ (-H) (by rw [abs_neg,abs_of_nonneg hH0])
  have hp := hJ H (abs_of_nonneg hH0)
  have hc := height_slab_partial_integrable _ H hH0 hleft
  refine ⟨hleft,?_⟩
  rw [hrow,←integral_add_compl hE hi]
  congr 2
  rw [height_slab_integral_pair _ H hH0 hi.integrableOn,
    height_slab_integral_pair _ H hH0 hleft]
  have heq : (fun q : ℝ×ℝ=>∫tx : ℝ in -H..H,k 2 ((tx,q.1),q.2))=
      (fun q : ℝ×ℝ=>(∫tx : ℝ in -H..H,k (a+16*e) ((tx,q.1),q.2))+
        I*((∫v : ℝ in (a+16*e)..2,k v ((-H,q.1),q.2))-(∫v : ℝ in (a+16*e)..2,k v ((H,q.1),q.2)))) := by
    funext q
    have hHT : H≤3*(i+1:ℕ)*B := by
      apply hH.trans
      have hn : (3*i+2:ℕ)≤3*(i+1) := by omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by linarith)
    simpa only [k,continuedRowOnLines,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using
      source_buffered_x_rectangle S hS hmax P hPS η u ψ B a e i he he' ha haTop hfirst hbin W0 W1 X Y Z hZ
        ((((1-a-6*e):ℝ):ℂ)+q.2*I) ((17/50:ℂ)+q.1*I) (by simp) (by norm_num) 2 H (by linarith) hH0 hHT
  rw [heq]
  dsimp only [k] at hm hp ⊢
  have hsplit := integral_add hc ((hm.sub hp).const_mul I)
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit,integral_const_mul]
  congr 1
  exact congrArg (fun z : ℂ=>I*z) (integral_sub hm hp)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1279
