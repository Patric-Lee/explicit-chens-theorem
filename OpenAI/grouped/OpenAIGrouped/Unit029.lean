import OpenAIGrouped.Unit028
import OpenAIGrouped.Unit009
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit026
import OpenAIGrouped.Unit017

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsHolomorphic.lean; sha256: 49e64d9cfd70b2f8449108732f13bd999cafe0d4f2bc80409d68741ba74f8698 -/
section Source1160
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p})

lemma rowMarkedTerm_differentiableAt (eta a rho : ℂ) (X W V : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hV : DifferentiableAt ℂ V t)
    (j e l k m : ℕ) :
    DifferentiableAt ℂ (fun s=>rowMarkedTerm p hp hg eta a (X s) (W s) (V s) rho j e l k m) t := by
  unfold rowMarkedTerm
  split_ifs
  · fun_prop
  · unfold rowWeightedScalar weightedScalar
    fun_prop

lemma rowBaseFinite_differentiableAt (eta a rho : ℂ) (X W V : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hV : DifferentiableAt ℂ V t)
    (hv : 1-V t≠0) (j e l : ℕ) :
    DifferentiableAt ℂ (fun s=>rowBaseFinite p hp hg eta a (X s) (W s) (V s) rho j e l) t := by
  have hd (k m : ℕ) := rowMarkedTerm_differentiableAt p hp hg eta a rho X W V t hX hW hV j e l k m
  unfold rowBaseFinite
  fun_prop (disch := assumption)

lemma rowClosedMarked_differentiableAt (eta a rho : ℂ) (X W V : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hV : DifferentiableAt ℂ V t)
    (hv : 1-V t≠0) (hr : 1-evenRatio (Ideal.absNorm (Ideal.span {p})) a (X t) (V t)≠0) (j : ℕ) :
    DifferentiableAt ℂ (fun s=>rowClosedMarked p hp hg eta a (X s) (W s) (V s) rho j) t := by
  have hd (e l : ℕ) := rowBaseFinite_differentiableAt p hp hg eta a rho X W V t hX hW hV hv j e l
  have hR : DifferentiableAt ℂ (fun s=>evenRatio (Ideal.absNorm (Ideal.span {p})) a (X s) (V s)) t := by
    unfold evenRatio
    fun_prop
  unfold rowClosedMarked
  fun_prop (disch := assumption)

lemma ramifiedClosed_differentiableAt (eta a rho : ℂ) (X W Z : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hZ : DifferentiableAt ℂ Z t)
    (hv : 1-coordV (Ideal.absNorm (Ideal.span {p})) (Z t)≠0)
    (hr : 1-coordR (Ideal.absNorm (Ideal.span {p})) (a^2) (X t) (Z t)≠0) (j : ℕ) :
    DifferentiableAt ℂ (fun s=>ramifiedClosed p hp hg eta a rho (X s) (W s) (Z s) j) t := by
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hcx : DifferentiableAt ℂ (fun s=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-X s)) t := by
    exact hX.neg.const_cpow (Or.inl (by exact_mod_cast hQ.ne'))
  have hcw : DifferentiableAt ℂ (fun s=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-W s)) t := by
    exact hW.neg.const_cpow (Or.inl (by exact_mod_cast hQ.ne'))
  have hcv := (coordV_differentiable _ hQ).differentiableAt.comp t hZ
  change DifferentiableAt ℂ (fun s=>coordV (Ideal.absNorm (Ideal.span {p})) (Z s)) t at hcv
  have hr' := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a (X t) (Z t)
  simp only [Complex.ofReal_natCast] at hr'
  have hd := rowClosedMarked_differentiableAt p hp hg eta a rho _ _ _ t hcx hcw hcv hv
    (by rw [hr'];exact hr) j
  unfold ramifiedClosed
  fun_prop

lemma ramifiedClosed_analytic_x (eta a rho w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hz : (4/25:ℝ)≤z.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun x=>ramifiedClosed p hp hg eta a rho x w z j) {x : ℂ|7/8<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx.le hz
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho id (fun _=>w) (fun _=>z) x
    differentiableAt_id (differentiableAt_const w) (differentiableAt_const z) hd.2.1 hd.1 j).differentiableWithinAt

lemma ramifiedClosed_analytic_w (eta a rho x z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1)
    (hx : (7/8:ℝ)≤x.re) (hz : (4/25:ℝ)≤z.re) (j : ℕ) :
    Differentiable ℂ (fun w=>ramifiedClosed p hp hg eta a rho x w z j) := by
  intro w
  have hd := open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz
  exact ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) id (fun _=>z) w
    (differentiableAt_const x) differentiableAt_id (differentiableAt_const z) hd.2.1 hd.1 j

lemma ramifiedClosed_analytic_z (eta a rho x w : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hx : (7/8:ℝ)≤x.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun z=>ramifiedClosed p hp hg eta a rho x w z j) {z : ℂ|4/25<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz.le
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) (fun _=>w) id z
    (differentiableAt_const x) (differentiableAt_const w) differentiableAt_id hd.2.1 hd.1 j).differentiableWithinAt

end SevenEighths.ProbeEuler
end

end OAI

end Source1160

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/Continuation.lean; sha256: 611130c5828aba5c9fb5f604af8bd15ce55b8fba1d57e5ae61769a184a18091d -/
section Source1161
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

lemma actualACube_norm_le (η : Character) (p : O) : ‖actualACube η p‖≤1 := by
  have h := actualAPhase_norm_le_one η p
  rw [←actualACube_sq,norm_pow] at h
  nlinarith [norm_nonneg (actualACube η p)]

theorem ramifiedCorrection_analytic_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (w z : ℂ) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>ramifiedCorrection η u P hs x w z) {x : ℂ | 7/8<x.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_x
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hz

theorem ramifiedCorrection_analytic_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hz : (4/25 : ℝ)≤z.re) :
    Differentiable ℂ (fun w =>ramifiedCorrection η u P hs x w z) := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_w
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx
  · exact hz

theorem ramifiedCorrection_analytic_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x w : ℂ) (hx : (7/8 : ℝ)≤x.re) :
    AnalyticOnNhd ℂ (fun z =>ramifiedCorrection η u P hs x w z) {z : ℂ | 4/25<z.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_z
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx

def ramifiedProduct (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏ P∈(ramifiedPrimes S u).attach,ramifiedCorrection η u P.val
    (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z

def continuedCorrection (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ramifiedProduct S hS η u x w z*unramifiedProduct S η u x w z

theorem continuedCorrection_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (η : Character) (u : FreeRow) (x w z : ℂ),
      (7/8 : ℝ)≤x.re → (19/20 : ℝ)≤w.re → (33/200 : ℝ)≤z.re →
      ‖continuedCorrection S hS η u x w z‖≤C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := ramified_product_subpower ε hε
  refine ⟨C*(3/2),by positivity,?_⟩
  intro S hS η u x w z hx hw hz
  have hR := hbound S hS η u x w z hx hw hz
  have hU := unramifiedProduct_defect S hS.tail η u x w z hx (by linarith) (by linarith)
  have hnorm : ‖unramifiedProduct S η u x w z‖≤3/2 := by
    have hh := norm_add_le (unramifiedProduct S η u x w z-1) (1 : ℂ)
    simp only [sub_add_cancel,norm_one] at hh
    linarith
  rw [continuedCorrection,norm_mul]
  apply (mul_le_mul hR hnorm (norm_nonneg _) (by positivity)).trans
  exact le_of_eq (by ring)

theorem continuedCorrection_analytic_x (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (w z : ℂ) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>continuedCorrection S hS η u x w z) {x : ℂ | 7/8<x.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_x S hS.tail η u w z hw hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact ramifiedCorrection_analytic_x η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) w z hz

theorem continuedCorrection_analytic_w (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (hx : (7/8 : ℝ)≤x.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w =>continuedCorrection S hS η u x w z) {w : ℂ | 9/10<w.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_w S hS.tail η u x z hx hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact (ramifiedCorrection_analytic_w η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x z hx hz).differentiableOn.analyticOnNhd
      (Complex.isOpen_re_gt _)

theorem continuedCorrection_analytic_z (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w : ℂ) (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) :
    AnalyticOnNhd ℂ (fun z =>continuedCorrection S hS η u x w z) {z : ℂ | 4/25<z.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_z S hS.tail η u x w hx hw)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact ramifiedCorrection_analytic_z η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x w hx

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1161

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/MarkedCoordinates.lean; sha256: 68b1c66ea47137b664a64c450a4e2075255f310f339e9953c0c4e544c3b150b3 -/
section Source1162
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def continuedMarkedLocal (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
    ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    (multiplicity p u.val)

theorem idealRowMarkedLocalFactor_eq_source (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    let p := primaryGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
    let hg := (supported_prime_data p hp hsp).1
    idealRowMarkedLocalFactor η u.val P x w z=
      rowMarkedSeries p hp hg (targetMonoid η p) (actualACube η p)
        ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
        (multiplicity p u.val) := by
  dsimp only
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  unfold idealRowMarkedLocalFactor rowMarkedSeries rowInner
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  change completedValuationMark P ((e.val,l),(k,m))*bareIdealHighSummand η u.val x w z
    (P.val^e.val) (P.val^l) (P.val^k) (P.val^m)=_
  have ht := bareIdealHighSummand_row_at_prime η p hp hg.1 hg.2 hprimary hsp
    (unitPart u p hp) (unitPart_coprime u p hp) (multiplicity p u.val) e.val l k m (by omega) x w z
  rw [←(canonical_decomposition u p hp).1] at ht
  conv_lhs at ht => rw [hspan]
  rw [ht]
  by_cases hzero : e.val+3*l=0
  · simp only [completedValuationMark,hzero,ne_eq,not_true_eq_false,ite_false,zero_mul,
      rowMarkedTerm,ite_true]
  · simp only [completedValuationMark,hzero,ne_eq,not_false_eq_true,ite_true,one_mul]
    simpa only [hspan] using sourceRowTerm_pos p hp hg.1 (targetMonoid η p) (actualACube η p)
      (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x w z
      (multiplicity p u.val) e.val l k m hzero

theorem continuedMarkedLocal_eq_initial (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedMarkedLocal η u P hs x w z=idealRowMarkedLocalFactor η u.val P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hρ := actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)
  have hgeom := row_initial_geometric η p hp hg.1 hg.2 (unitPart u p hp)
    (unitPart_coprime u p hp) x w z hx hw hz
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) :=
    HeckeDyadic.norm_pos ⟨Ideal.span {p},Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero⟩
  have he := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (actualACube η p) x z
  simp only [Complex.ofReal_natCast] at he
  have hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [he]
    exact hgeom.2.1
  rw [idealRowMarkedLocalFactor_eq_source η u P hs x w z]
  unfold continuedMarkedLocal
  symm
  simpa only [hspan] using rowMarkedSeries_eq_closed p hp hg.1 hg.2 (targetMonoid η p)
    (actualACube η p) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
    _ hρ hgeom.1 hR (multiplicity p u.val) (multiplicity_lt_six u p hp)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1162

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/Agreement.lean; sha256: d3fbdbeae80d4d075ef3a7a52e1714c71ae5e764aa921ac566bb1da8026173b0 -/
section Source1163
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def ramifiedIndices (S : Finset (Ideal O)) (u : FreeRow) : Finset {P : PrimeIdeal // P.val∉S} :=
  (SmoothMobiusCorrection.primeSet (Ideal.span {u.val})).subtype (fun P => P.val∉S)

theorem mem_ramifiedIndices (S : Finset (Ideal O)) (u : FreeRow)
    (P : {P : PrimeIdeal // P.val∉S}) : P∈ramifiedIndices S u ↔ P.val.val∣Ideal.span {u.val} := by
  simp only [ramifiedIndices,Finset.mem_subtype,SmoothMobiusCorrection.mem_primeSet,
    IdealMobiusDivisorSum.primeSupport,Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff
      (show (Ideal.span {u.val}:Ideal O)≠0 from Ideal.span_singleton_eq_bot.not.mpr u.property.1),
    P.val.property,true_and]

def ramifiedFactor (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (P : {P : PrimeIdeal // P.val∉S}) (x w z : ℂ) : ℂ :=
  if P.val.val∣Ideal.span {u.val} then
    ramifiedCorrection η u P.val (outside_prime_supported S hS.bad P.val P.property) x w z else 1

theorem ramifiedFactor_hasProd (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    HasProd (fun P =>ramifiedFactor S hS η u P x w z) (ramifiedProduct S hS η u x w z) := by
  have he : (∏ P∈ramifiedIndices S u,ramifiedFactor S hS η u P x w z)=
      ramifiedProduct S hS η u x w z := by
    unfold ramifiedProduct
    apply Finset.prod_bij (fun P hP =>
      (⟨P.val,Finset.mem_filter.mpr ⟨Finset.mem_subtype.mp hP,P.property⟩⟩ : ramifiedPrimes S u))
    · intro P hP; exact Finset.mem_attach _ _
    · intro P hP Q hQ heq
      exact Subtype.ext (congrArg (fun R : ramifiedPrimes S u => R.val) heq)
    · intro P hP
      refine ⟨⟨P.val,(Finset.mem_filter.mp P.property).2⟩,?_,?_⟩
      · exact Finset.mem_subtype.mpr (Finset.mem_filter.mp P.property).1
      · rfl
    · intro P hP
      simp only [ramifiedFactor,ite_eq_left ((mem_ramifiedIndices S u P).mp hP)]
  rw [←he]
  apply hasProd_prod_of_ne_finset_one
  intro P hP
  exact ite_eq_right (fun hd => hP ((mem_ramifiedIndices S u P).mpr hd))

theorem supported_prime_coprime (P : PrimeIdeal) (hs : Supported P.val) (u : O)
    (hn : ¬P.val∣Ideal.span {u}) : IsCoprime P.val (Ideal.span {u}) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have he : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  have hnot : ¬p∣u := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←he,Ideal.span_singleton_le_span_singleton]
    exact hd
  rw [←he,Ideal.isCoprime_span_singleton_iff]
  exact hp.irreducible.coprime_iff_not_dvd.mpr hnot

theorem continuedCorrection_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedCorrection S hS η u x w z=globalCorrection S η u x w z := by
  have hr := ramifiedFactor_hasProd S hS η u x w z
  have hu := (unramifiedProduct_multipliable S hS.tail η u x w z
    (by linarith) (by linarith) (by linarith)).hasProd
  have he := hr.mul hu
  have hlocal (P : {P : PrimeIdeal // P.val∉S}) :
      ramifiedFactor S hS η u P x w z*unramifiedFactor η u P.val x w z=
        localCorrection η u P.val x w z := by
    have hs := outside_prime_supported S hS.bad P.val P.property
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simp only [ramifiedFactor,unramifiedFactor,ite_eq_left h,mul_one]
      exact (localCorrection_eq_ramified η u P.val hs h x w z hx hw hz).symm
    · simp only [ramifiedFactor,unramifiedFactor,ite_eq_right h,one_mul]
      exact (localCorrection_unramified_ideal η u P.val hs
        (supported_prime_coprime P.val hs u.val h) x w z hx hw hz).symm
  have hh : HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>localCorrection η u P.val x w z)
      (continuedCorrection S hS η u x w z) := by
    simpa only [hlocal,continuedCorrection,unramifiedProduct] using he
  exact hh.tprod_eq.symm

theorem high_L_factorization_continued (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η u.val x w z=
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (rowCharacter S hS.prime u) w /
        LFunction ((targetRow η u).excludePrimes S hS.prime) x*continuedCorrection S hS η u x w z := by
  rw [continuedCorrection_eq_initial S hS η u x w z hx hw hz]
  exact high_L_factorization S hS.prime hS.bad η u x w z hx hw hz

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1163

/- Original source: OAI/NumberTheory/DirichletL/PrincipalSlotEstimate.lean; sha256: cf5f5e473a2d9ae46c0b4628824eb3c2fbed706a4698179397cb075b86e8fb6e -/
section Source1164
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex

namespace SevenEighths.PrincipalSlotEstimate
open ProbeEuler ProbeLocal

def principalMarked (Q : ℝ) (A η s : ℂ) : ℂ :=
  markedFactor (coordR Q A s (1 / 6)) (coordV Q (1 / 6)) (Q : ℂ)⁻¹
    (coordK Q η s 1) (-coordD Q η 1 s + coordW Q 1 1 * coordR Q A s (1 / 6)) 1

def principalReplacement (Q : ℝ) (A η s : ℂ) : ℂ :=
  compensatedReplacement (coordV Q (1 / 6)) (coordW Q 1 1) (coordD Q η 1 s)
    (principalMarked Q A η s) (star η * (Q : ℂ) ^ s) ((Q : ℂ) ^ (-1 : ℂ))

def principalSlot (Q : ℝ) (A η s : ℂ) : ℂ :=
  principalReplacement Q A η s / unramifiedClosed Q A η 1 s 1 (1 / 6)

theorem principal_correction_defect {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    ‖unramifiedClosed Q A η 1 s 1 (1 / 6) - 1‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have h := unramifiedClosed_second_region_bound Q A η 1 s 1 (1 / 6)
    (by linarith) hA hη (by simp) hs (by norm_num) (by norm_num)
  calc
    _ ≤ 240 * Q ^ (-(363 / 200 : ℝ)) := h
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem principal_correction_lower_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ := by
  have h := principal_correction_defect hQ hA hη hs
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s 1 (1 / 6))
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem principal_correction_ne_zero {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (principal_correction_lower_bound hQ hA hη hs)

theorem principal_correction_inverse_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    ‖(unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹‖ ≤ 2 := by
  have hl := principal_correction_lower_bound hQ hA hη hs
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖)).mpr
  linarith

theorem unit_phase_inverse (η : ℂ) (hη : ‖η‖ = 1) : star η * η = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hη]
  norm_num

theorem principal_coord_cancellation {Q : ℝ} (hQ : 0 < Q) (η s : ℂ) (hη : ‖η‖ = 1) :
    (star η * (Q : ℂ) ^ s) * coordD Q η 1 s = 1 := by
  have hQ0 : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  unfold coordD
  simp only [star_one, mul_one]
  calc
    _ = (star η * η) * ((Q : ℂ) ^ s * (Q : ℂ) ^ (-s)) := by ring
    _ = 1 := by rw [unit_phase_inverse η hη, ← Complex.cpow_add _ _ hQ0]; simp

theorem principal_V {Q : ℝ} : coordV Q (1 / 6) = (Q : ℂ)⁻¹ := by
  norm_num [coordV, Complex.cpow_neg_one]

theorem principal_W {Q : ℝ} : coordW Q 1 1 = (Q : ℂ)⁻¹ := by
  simp [coordW, Complex.cpow_neg_one]

theorem principal_B_norm {Q : ℝ} (hQ : 0 < Q) (η s : ℂ) (hη : ‖η‖ = 1) :
    ‖star η * (Q : ℂ) ^ s‖ = Q ^ s.re := by
  rw [norm_mul, norm_star, hη, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]

theorem compensated_unit_error_bound (V W D P B q : ℂ) (T : ℝ)
    (_hT : 0 ≤ T) (hV : ‖V‖ ≤ 1 / 2) (hW : ‖W‖ ≤ 1)
    (hD : ‖D‖ ≤ 1 / 2) (hq : ‖q‖ ≤ 1)
    (hVT : ‖V‖ ≤ T) (hDT : ‖D‖ ≤ T)
    (hE : ‖P + D‖ ≤ 28 * T) (hBE : ‖B‖ * ‖P + D‖ ≤ 28 * T)
    (hBD : B * D = 1) (hWq : W = q) :
    ‖compensatedReplacement V W D P B q + continuedCorrection V W D P‖ ≤ 720 * T := by
  have h1V : ‖1 - V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have h1W : ‖1 - W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have h1q : ‖1 - q‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) q
    simp only [norm_one] at this
    linarith
  have hiV := inv_one_sub_norm_le_two V hV
  have hiD := inv_one_sub_norm_le_two D hD
  have hfac : ‖(1 - V) * (1 - W) / (1 - D)‖ ≤ 8 := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc
      ‖1 - V‖ * ‖1 - W‖ * ‖(1 - D)⁻¹‖ ≤ (2 : ℝ) * 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have hleft : ‖(1 - q) * (V / (1 - V) - D)‖ ≤ 6 * T := by
    calc
      _ = ‖1 - q‖ * ‖V / (1 - V) - D‖ := norm_mul _ _
      _ ≤ 2 * (‖V‖ * 2 + ‖D‖) := by
        gcongr
        calc
          _ ≤ ‖V / (1 - V)‖ + ‖D‖ := norm_sub_le _ _
          _ ≤ _ := by rw [div_eq_mul_inv, norm_mul]; gcongr
      _ ≤ 6 * T := by linarith
  have hright : ‖(B + 1 - q) * (P + D)‖ ≤ 84 * T := by
    have hc : ‖B + 1 - q‖ ≤ ‖B‖ + 2 := by
      calc
        _ = ‖B + (1 - q)‖ := by congr 1; ring
        _ ≤ ‖B‖ + ‖1 - q‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    calc
      _ = ‖B + 1 - q‖ * ‖P + D‖ := norm_mul _ _
      _ ≤ (‖B‖ + 2) * ‖P + D‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ 84 * T := by nlinarith
  have hid := continued_normalized_cancellation V W D P B q 1
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD)
    hBD (by simpa using hWq)
  simp only [mul_one] at hid
  rw [hid, norm_mul]
  calc
    _ ≤ 8 * (‖(1 - q) * (V / (1 - V) - D)‖ + ‖(B + 1 - q) * (P + D)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 720 * T := by linarith

theorem principal_marked_error_bounds {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re) :
    ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ 28 * Q ^ (-(7 / 8 : ℝ)) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      28 * Q ^ (-(7 / 8 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by
    have h := coordW_norm_le Q hQ0 (1 : ℂ) 1 (by simp)
    norm_num at h
    exact h.trans (by simpa using hpow (-1) 0 (by norm_num))
  have hR : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (3 - 6 * s.re) := by
    convert coordR_norm_le Q hQ0 A s (1 / 6) hA using 1
    norm_num
    congr 1
    ring
  have hD : ‖coordD Q η 1 s‖ ≤ Q ^ (-s.re) :=
    coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hK : ‖coordK Q η s 1‖ ≤ Q ^ (-s.re) := by
    convert coordK_norm_le Q hQ1 η s 1 hη.le using 1
    norm_num
  have hB := principal_B_norm hQ0 η s hη
  have hRhalf : ‖coordR Q A s (1 / 6)‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q (3 - 6 * s.re) hQ4 (by linarith))
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by norm_num)
  have hDhalf : ‖coordD Q η 1 s‖ ≤ 1 / 2 :=
    hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [← principal_V]; linarith
  have hE := unramified_marked_error_bound (coordR Q A s (1 / 6))
    (coordV Q (1 / 6)) (Q : ℂ)⁻¹ (coordK Q η s 1) (coordW Q 1 1)
    (coordD Q η 1 s) hRhalf hVhalf hq hDhalf
  change ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (-(7 / 8 : ℝ)) :=
    hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖ ≤ Q ^ (-(7 / 8 : ℝ)) := by
    calc
      _ ≤ Q ^ (-s.re) * Q ^ (-1 : ℝ) := by rw [hV]; gcongr
      _ = Q ^ (-s.re - 1) := by rw [← Real.rpow_add hQ0]; congr 1
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s (1 / 6)‖ ≤
      Q ^ (-(7 / 8 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (3 - 6 * s.re) := by rw [hB]; gcongr
      _ = Q ^ (3 - 5 * s.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ *
      (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) ≤ Q ^ (-(7 / 8 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (-s.re) * Q ^ (-1 : ℝ)) := by rw [hB, hV]; gcongr
      _ = Q ^ (-1 : ℝ) := by rw [← mul_assoc, ← Real.rpow_add hQ0]; simp
      _ ≤ _ := hpow _ _ (by norm_num)
  have hE' : ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s (1 / 6)‖ + 4 * (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s (1 / 6)))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem principal_replacement_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re) :
    ‖principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      720 * Q ^ (-(7 / 8 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by norm_num)
  have hD := coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hDhalf := hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hWq : coordW Q 1 1 = (Q : ℂ) ^ (-1 : ℂ) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-1 : ℂ)‖ ≤ 1 := by
    rw [Complex.cpow_neg_one, ← principal_V]; linarith
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by rw [hWq]; exact hq
  have hVT : ‖coordV Q (1 / 6)‖ ≤ Q ^ (-(7 / 8 : ℝ)) := by
    rw [hV]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-(7 / 8 : ℝ)) :=
    hD.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := principal_marked_error_bounds hQ hA hη hs
  exact compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hVhalf hW hDhalf hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 η s hη) hWq

theorem principal_slot_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re) :
    ‖principalSlot Q A η s + 1‖ ≤ 1440 * Q ^ (-(7 / 8 : ℝ)) := by
  have hn := principal_correction_ne_zero hQ hA hη.le hs
  have he := principal_replacement_error hQ hA hη hs
  have hi := principal_correction_inverse_bound hQ hA hη.le hs
  have hid : principalSlot Q A η s + 1 =
      (principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)) *
        (unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹ := by
    unfold principalSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-(7 / 8 : ℝ))) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem actual_target_norm (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) :
    ‖HeckeFamily.elementCoeff η p‖ = 1 := by
  let : Finite (HeckeFamily.O ⧸ η.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ η.modulus) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := hp
  unfold HeckeFamily.elementCoeff
  rw [← hu]
  exact FiniteRayExpansion.norm_char_unit η.residue u

theorem actual_principal_slot_error (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) (s : ℂ)
    (hQ : 480 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)) (hs : 7 / 8 ≤ s.re) :
    ‖principalSlot (Ideal.absNorm (Ideal.span {p})) (actualAPhase η p)
      (HeckeFamily.elementCoeff η p) s + 1‖ ≤
      1440 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(7 / 8 : ℝ)) :=
  principal_slot_error hQ (actualAPhase_norm_le_one η p) (actual_target_norm η p hp) hs

theorem weighted_slot_error {ι : Type*} (S : Finset ι) (w : ι → ℝ) (B : ι → ℂ)
    (δ : ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (hB : ∀ i ∈ S, ‖B i + 1‖ ≤ δ) :
    ‖(∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ)‖ ≤
      δ * ∑ i ∈ S, w i := by
  have hid : (∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ) =
      ∑ i ∈ S, (w i : ℂ) * (B i + 1) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, Complex.ofReal_sum]
  rw [hid]
  calc
    _ ≤ ∑ i ∈ S, ‖(w i : ℂ) * (B i + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, δ * w i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hB i hi) (hw i hi)
    _ = _ := by rw [Finset.mul_sum]

theorem weighted_slot_relative_error {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (B : ι → ℂ) (δ : ℝ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hB : ∀ i ∈ S, ‖B i + 1‖ ≤ δ) (hS : 0 < ∑ i ∈ S, w i) :
    ‖(∑ i ∈ S, (w i : ℂ) * B i) / (-(∑ i ∈ S, w i : ℝ) : ℂ) - 1‖ ≤ δ := by
  have hSc : ((∑ i ∈ S, w i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  have hid : (∑ i ∈ S, (w i : ℂ) * B i) / (-(∑ i ∈ S, w i : ℝ) : ℂ) - 1 =
      -((∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ)) /
        (∑ i ∈ S, w i : ℝ) := by field_simp; ring
  rw [hid, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  exact (div_le_iff₀ hS).mpr (weighted_slot_error S w B δ hw hB)

theorem weighted_principal_slot_error {ι : Type*} (S : Finset ι) (w Q : ι → ℝ)
    (A η : ι → ℂ) (s : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : 7 / 8 ≤ s.re) :
    ‖(∑ i ∈ S, (w i : ℂ) * principalSlot (Q i) (A i) (η i) s) +
        (∑ i ∈ S, w i : ℝ)‖ ≤
      (1440 * P ^ (-(7 / 8 : ℝ))) * ∑ i ∈ S, w i := by
  apply weighted_slot_error S w _ _ hw
  intro i hi
  apply (principal_slot_error (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by norm_num)

theorem product_error {κ : Type*} (S : Finset κ) (F : κ → ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hF : ∀ i ∈ S, ‖F i - 1‖ ≤ δ) :
    ‖(∏ i ∈ S, F i) - 1‖ ≤ (1 + δ) ^ S.card - 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have haF := hF a (Finset.mem_insert_self a S)
    have hSF : ∀ i ∈ S, ‖F i - 1‖ ≤ δ := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hprod := ih hSF
    have haN : ‖F a‖ ≤ 1 + δ := by
      have h := norm_sub_norm_le (F a) (1 : ℂ)
      simp only [norm_one] at h
      linarith
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      _ = ‖F a * ((∏ i ∈ S, F i) - 1) + (F a - 1)‖ := by congr 1; ring
      _ ≤ ‖F a * ((∏ i ∈ S, F i) - 1)‖ + ‖F a - 1‖ := norm_add_le _ _
      _ ≤ (1 + δ) * ((1 + δ) ^ S.card - 1) + δ := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul haN hprod (norm_nonneg _) (by linarith)) haF
      _ = _ := by rw [pow_succ]; ring

theorem product_error_linear (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (1 + δ) ^ n - 1 ≤ n * 2 ^ n * δ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hbase : 0 ≤ (1 + δ) ^ n - 1 := by
      exact sub_nonneg.mpr (one_le_pow₀ (by linarith))
    calc
      _ = (1 + δ) * ((1 + δ) ^ n - 1) + δ := by rw [pow_succ]; ring
      _ ≤ 2 * ((n : ℝ) * 2 ^ n * δ) + δ := by
        gcongr
        linarith
      _ ≤ _ := by rw [Nat.cast_succ, pow_succ]; nlinarith

def principalScalar {κ : Type*} (S : Finset κ) (M : κ → ℝ) : ℂ :=
  (-1 : ℂ) ^ S.card * (∏ i ∈ S, M i : ℝ)

theorem principalScalar_eq {κ : Type*} (S : Finset κ) (M : κ → ℝ) :
    principalScalar S M = ∏ i ∈ S, (-(M i : ℂ)) := by
  unfold principalScalar
  rw [Complex.ofReal_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem principalScalar_ne_zero {κ : Type*} (S : Finset κ) (M : κ → ℝ)
    (hM : ∀ i ∈ S, 0 < M i) : principalScalar S M ≠ 0 := by
  rw [principalScalar_eq]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (hM i hi).ne')

theorem fixed_product_relative_error {κ : Type*} (S : Finset κ)
    (M : κ → ℝ) (W : κ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ i ∈ S, 0 < M i)
    (hW : ∀ i ∈ S, ‖W i + (M i : ℂ)‖ ≤ δ * M i) :
    ‖(∏ i ∈ S, W i) / principalScalar S M - 1‖ ≤ (1 + δ) ^ S.card - 1 := by
  rw [principalScalar_eq, ← Finset.prod_div_distrib]
  apply product_error S _ δ hδ
  intro i hi
  have hMi : (M i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM i hi).ne'
  have hid : W i / (-(M i : ℂ)) - 1 = -(W i + (M i : ℂ)) / (M i : ℂ) := by
    field_simp
    ring
  rw [hid, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hM i hi)]
  exact (div_le_iff₀ (hM i hi)).mpr (hW i hi)

theorem fixed_product_relative_error_linear {κ : Type*} (S : Finset κ)
    (M : κ → ℝ) (W : κ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : ∀ i ∈ S, 0 < M i)
    (hW : ∀ i ∈ S, ‖W i + (M i : ℂ)‖ ≤ δ * M i) :
    ‖(∏ i ∈ S, W i) / principalScalar S M - 1‖ ≤ S.card * 2 ^ S.card * δ :=
  (fixed_product_relative_error S M W δ hδ hM hW).trans
    (product_error_linear S.card hδ hδ1)

theorem weighted_principal_product_error {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : 7 / 8 ≤ s.re)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      (1 + 1440 * P ^ (-(7 / 8 : ℝ))) ^ S.card - 1 := by
  apply fixed_product_relative_error S _ _ _ (by positivity) hM
  intro j hj
  exact weighted_principal_slot_error (T j) (w j) (Q j) (A j) (η j) s P hP
    (hw j hj) (hQ j hj) (hA j hj) (hη j hj) hs

def principalRawFactor (Q : ℝ) (A η s : ℂ) : ℂ :=
  localFactor (coordV Q (1 / 6)) (coordW Q 1 1) (principalMarked Q A η s)

theorem principal_geometric_bounds {Q : ℝ} {η s : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    ‖coordV Q (1 / 6)‖ ≤ 1 / 2 ∧ ‖coordW Q 1 1‖ ≤ 1 / 2 ∧
      ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    norm_num
    exact rpow_le_half Q (-1) hQ4 (by norm_num)
  refine ⟨hV, ?_, ?_⟩
  · rw [principal_W, ← principal_V]; exact hV
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans
      (rpow_le_half Q (-s.re) hQ4 (by linarith))

theorem principal_correction_eq_raw {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) =
      localCorrection (coordV Q (1 / 6)) (coordW Q 1 1) (coordD Q η 1 s)
        (principalMarked Q A η s) := by
  have h := principal_geometric_bounds hQ hη hs
  exact continuedCorrection_eq_raw _ _ _ _
    (one_sub_ne_zero_of_norm_le_half _ h.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.2)

theorem principal_raw_lower_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    1 / 16 ≤ ‖principalRawFactor Q A η s‖ := by
  have hl := principal_correction_lower_bound hQ hA hη hs
  have hg := principal_geometric_bounds hQ hη hs
  have hV : ‖1 - coordV Q (1 / 6)‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordV Q (1 / 6))
    simp only [norm_one] at this
    linarith [hg.1]
  have hW : ‖1 - coordW Q 1 1‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordW Q 1 1)
    simp only [norm_one] at this
    linarith [hg.2.1]
  have hD := inv_one_sub_norm_le_two (coordD Q η 1 s) hg.2.2
  have hupper : ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      8 * ‖principalRawFactor Q A η s‖ := by
    rw [principal_correction_eq_raw hQ hη hs]
    unfold localCorrection
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul]
    change ‖principalRawFactor Q A η s‖ *
      (‖1 - coordV Q (1 / 6)‖ * ‖1 - coordW Q 1 1‖) * ‖(1 - coordD Q η 1 s)⁻¹‖ ≤ _
    calc
      _ ≤ ‖principalRawFactor Q A η s‖ * (2 * 2) * 2 := by gcongr
      _ = _ := by ring
  linarith

theorem principal_raw_ne_zero {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    principalRawFactor Q A η s ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 16).trans_le
    (principal_raw_lower_bound hQ hA hη hs)

theorem principal_slot_eq_raw {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    principalSlot Q A η s =
      (star η * (Q : ℂ) ^ s) * principalMarked Q A η s / principalRawFactor Q A η s -
        (Q : ℂ) ^ (-1 : ℂ) := by
  have hg := principal_geometric_bounds hQ hη hs
  have hn := principal_correction_ne_zero hQ hA hη hs
  have hp := principal_raw_ne_zero hQ hA hη hs
  have hr := compensatedReplacement_eq_raw (coordV Q (1 / 6)) (coordW Q 1 1)
    (coordD Q η 1 s) (principalMarked Q A η s) (star η * (Q : ℂ) ^ s)
    ((Q : ℂ) ^ (-1 : ℂ))
    (one_sub_ne_zero_of_norm_le_half _ hg.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.2) hp
  rw [← principal_correction_eq_raw hQ hη hs] at hr
  unfold principalSlot principalReplacement
  rw [hr]
  exact mul_div_cancel_left₀ _ hn

theorem principal_raw_slot_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re) :
    ‖(star η * (Q : ℂ) ^ s) * principalMarked Q A η s / principalRawFactor Q A η s -
        (Q : ℂ) ^ (-1 : ℂ) + 1‖ ≤ 1440 * Q ^ (-(7 / 8 : ℝ)) := by
  rw [← principal_slot_eq_raw hQ hA hη.le hs]
  exact principal_slot_error hQ hA hη hs

theorem weighted_principal_product_error_linear {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : 7 / 8 ≤ s.re)
    (hsmall : 1440 * P ^ (-(7 / 8 : ℝ)) ≤ 1)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      S.card * 2 ^ S.card * (1440 * P ^ (-(7 / 8 : ℝ))) :=
  (weighted_principal_product_error S T w Q A η s P hP hs hw hQ hA hη hM).trans
    (product_error_linear S.card (by positivity) hsmall)

def regionMarked (Q : ℝ) (A η s w z : ℂ) : ℂ :=
  markedFactor (coordR Q A s z) (coordV Q z) (Q : ℂ)⁻¹ (coordK Q η s w)
    (-coordD Q η 1 s + coordW Q 1 w * coordR Q A s z) 1

def regionReplacement (Q : ℝ) (A η s w z : ℂ) : ℂ :=
  compensatedReplacement (coordV Q z) (coordW Q 1 w) (coordD Q η 1 s)
    (regionMarked Q A η s w z) (star η * (Q : ℂ) ^ s) ((Q : ℂ) ^ (-w))

def regionSlot (Q : ℝ) (A η s w z : ℂ) : ℂ :=
  regionReplacement Q A η s w z / unramifiedClosed Q A η 1 s w z

def regionRawFactor (Q : ℝ) (A η s w z : ℂ) : ℂ :=
  localFactor (coordV Q z) (coordW Q 1 w) (regionMarked Q A η s w z)

theorem region_correction_defect {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖unramifiedClosed Q A η 1 s w z - 1‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  calc
    _ ≤ 240 * Q ^ (-(363 / 200 : ℝ)) :=
      unramifiedClosed_second_region_bound Q A η 1 s w z (by linarith) hA hη (by simp) hs hw hz
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem region_correction_lower_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s w z‖ := by
  have h := region_correction_defect hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem region_correction_ne_zero {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    unramifiedClosed Q A η 1 s w z ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (region_correction_lower_bound hQ hA hη hs hw hz)

theorem region_correction_inverse_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖(unramifiedClosed Q A η 1 s w z)⁻¹‖ ≤ 2 := by
  have hl := region_correction_lower_bound hQ hA hη hs hw hz
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s w z‖)).mpr
  linarith

theorem region_geometric_bounds {Q : ℝ} {η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖coordV Q z‖ ≤ 1 / 2 ∧ ‖coordW Q 1 w‖ ≤ 1 / 2 ∧ ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ4 (by linarith)
  · exact (coordW_norm_le Q hQ0 1 w (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))

theorem region_marked_error_bounds {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ 28 * Q ^ (-(7 / 8 : ℝ)) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      28 * Q ^ (-(7 / 8 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV := coordV_norm Q hQ0 z
  have hR := coordR_norm_le Q hQ0 A s z hA
  have hK := coordK_norm_le Q hQ1 η s w hη.le
  have hB := principal_B_norm hQ0 η s hη
  have hg := region_geometric_bounds hQ hη.le hs hw hz
  have hRhalf : ‖coordR Q A s z‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q _ hQ4 (by linarith))
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have hE := unramified_marked_error_bound (coordR Q A s z) (coordV Q z)
    (Q : ℂ)⁻¹ (coordK Q η s w) (coordW Q 1 w) (coordD Q η 1 s)
    hRhalf hg.1 hq hg.2.2
  change ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s z‖ ≤ Q ^ (-(7 / 8 : ℝ)) := hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s w‖ * ‖coordV Q z‖ ≤ Q ^ (-(7 / 8 : ℝ)) := by
    calc
      _ ≤ Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re) := by rw [hV]; gcongr
      _ = Q ^ (1 - s.re - w.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s z‖ ≤ Q ^ (-(7 / 8 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (4 - 6 * s.re - 6 * z.re) := by rw [hB]; gcongr
      _ = Q ^ (4 - 5 * s.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ * (‖coordK Q η s w‖ * ‖coordV Q z‖) ≤
      Q ^ (-(7 / 8 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re)) := by rw [hB, hV]; gcongr
      _ = Q ^ (1 - w.re - 6 * z.re) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hE' : ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s z‖ + 4 * (‖coordK Q η s w‖ * ‖coordV Q z‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s z))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem region_replacement_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z‖ ≤
      720 * Q ^ (-(7 / 8 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hg := region_geometric_bounds hQ hη.le hs hw hz
  have hWq : coordW Q 1 w = (Q : ℂ) ^ (-w) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-w)‖ ≤ 1 := by rw [← hWq]; linarith [hg.2.1]
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hVT : ‖coordV Q z‖ ≤ Q ^ (-(7 / 8 : ℝ)) := by
    rw [coordV_norm Q hQ0]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-(7 / 8 : ℝ)) :=
    (coordD_norm_le Q hQ0 η 1 s hη.le (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := region_marked_error_bounds hQ hA hη hs hw hz
  exact compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hg.1 hW hg.2.2 hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 η s hη) hWq

theorem region_slot_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z + 1‖ ≤ 1440 * Q ^ (-(7 / 8 : ℝ)) := by
  have hn := region_correction_ne_zero hQ hA hη.le hs hw hz
  have he := region_replacement_error hQ hA hη hs hw hz
  have hi := region_correction_inverse_bound hQ hA hη.le hs hw hz
  have hid : regionSlot Q A η s w z + 1 =
      (regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z) *
        (unramifiedClosed Q A η 1 s w z)⁻¹ := by
    unfold regionSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-(7 / 8 : ℝ))) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

@[simp] theorem region_slot_at_residue (Q : ℝ) (A η s : ℂ) :
    regionSlot Q A η s 1 (1 / 6) = principalSlot Q A η s := rfl

theorem region_correction_eq_raw {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    unramifiedClosed Q A η 1 s w z =
      localCorrection (coordV Q z) (coordW Q 1 w) (coordD Q η 1 s)
        (regionMarked Q A η s w z) := by
  have h := region_geometric_bounds hQ hη hs hw hz
  exact continuedCorrection_eq_raw _ _ _ _
    (one_sub_ne_zero_of_norm_le_half _ h.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.2)

theorem region_raw_lower_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    1 / 16 ≤ ‖regionRawFactor Q A η s w z‖ := by
  have hl := region_correction_lower_bound hQ hA hη hs hw hz
  have hg := region_geometric_bounds hQ hη hs hw hz
  have hV : ‖1 - coordV Q z‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordV Q z)
    simp only [norm_one] at this
    linarith [hg.1]
  have hW : ‖1 - coordW Q 1 w‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordW Q 1 w)
    simp only [norm_one] at this
    linarith [hg.2.1]
  have hD := inv_one_sub_norm_le_two (coordD Q η 1 s) hg.2.2
  have hupper : ‖unramifiedClosed Q A η 1 s w z‖ ≤
      8 * ‖regionRawFactor Q A η s w z‖ := by
    rw [region_correction_eq_raw hQ hη hs hw hz]
    unfold localCorrection
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul]
    change ‖regionRawFactor Q A η s w z‖ *
      (‖1 - coordV Q z‖ * ‖1 - coordW Q 1 w‖) * ‖(1 - coordD Q η 1 s)⁻¹‖ ≤ _
    calc
      _ ≤ ‖regionRawFactor Q A η s w z‖ * (2 * 2) * 2 := by gcongr
      _ = _ := by ring
  linarith

theorem region_raw_ne_zero {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    regionRawFactor Q A η s w z ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 16).trans_le
    (region_raw_lower_bound hQ hA hη hs hw hz)

theorem region_slot_eq_raw {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    regionSlot Q A η s w z =
      (star η * (Q : ℂ) ^ s) * regionMarked Q A η s w z / regionRawFactor Q A η s w z -
        (Q : ℂ) ^ (-w) := by
  have hg := region_geometric_bounds hQ hη hs hw hz
  have hn := region_correction_ne_zero hQ hA hη hs hw hz
  have hp := region_raw_ne_zero hQ hA hη hs hw hz
  have hr := compensatedReplacement_eq_raw (coordV Q z) (coordW Q 1 w)
    (coordD Q η 1 s) (regionMarked Q A η s w z) (star η * (Q : ℂ) ^ s)
    ((Q : ℂ) ^ (-w))
    (one_sub_ne_zero_of_norm_le_half _ hg.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.2) hp
  rw [← region_correction_eq_raw hQ hη hs hw hz] at hr
  unfold regionSlot regionReplacement
  rw [hr]
  exact mul_div_cancel_left₀ _ hn

theorem region_raw_slot_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖(star η * (Q : ℂ) ^ s) * regionMarked Q A η s w z / regionRawFactor Q A η s w z -
        (Q : ℂ) ^ (-w) + 1‖ ≤ 1440 * Q ^ (-(7 / 8 : ℝ)) := by
  rw [← region_slot_eq_raw hQ hA hη.le hs hw hz]
  exact region_slot_error hQ hA hη hs hw hz

theorem region_slot_norm_le {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z‖ ≤ 1 + 1440 * Q ^ (-(7 / 8 : ℝ)) := by
  have he := region_slot_error hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (regionSlot Q A η s w z) (-1 : ℂ)
  simp only [norm_neg, norm_one, sub_neg_eq_add] at hn
  linarith

theorem weighted_region_slot_norm {ι : Type*} (S : Finset ι) (b Q : ι → ℝ)
    (A η : ι → ℂ) (s w z : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hb : ∀ i ∈ S, 0 ≤ b i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : 7 / 8 ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖∑ i ∈ S, (b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ ≤
      (1 + 1440 * P ^ (-(7 / 8 : ℝ))) * ∑ i ∈ S, b i * (Q i) ^ (z.re - 1) := by
  calc
    _ ≤ ∑ i ∈ S, ‖(b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ S, (1 + 1440 * P ^ (-(7 / 8 : ℝ))) * (b i * (Q i) ^ (z.re - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hQi : 0 < Q i := by linarith [hQ i hi]
      have he := region_slot_norm_le (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs hw hz
      have he' : ‖regionSlot (Q i) (A i) (η i) s w z‖ ≤ 1 + 1440 * P ^ (-(7 / 8 : ℝ)) := by
        apply he.trans
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by norm_num)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb i hi),
        Complex.norm_cpow_eq_rpow_re_of_pos hQi]
      simp only [Complex.sub_re, Complex.one_re]
      exact (mul_le_mul_of_nonneg_left he'
        (mul_nonneg (hb i hi) (Real.rpow_nonneg hQi.le _))).trans_eq (mul_comm _ _)
    _ = _ := by rw [Finset.mul_sum]

theorem actual_region_slot_error (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) (s w z : ℂ)
    (hQ : 480 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot (Ideal.absNorm (Ideal.span {p})) (actualAPhase η p)
      (HeckeFamily.elementCoeff η p) s w z + 1‖ ≤
      1440 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(7 / 8 : ℝ)) :=
  region_slot_error hQ (actualAPhase_norm_le_one η p) (actual_target_norm η p hp) hs hw hz

end SevenEighths.PrincipalSlotEstimate

end

end OAI

end Source1164

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsSelectedCancellation.lean; sha256: ca7305c7bcbf881ec53c7d49afb8992d30fdbc9bde2156ba24244ca7b34925ba -/
section Source1165
namespace OAI

noncomputable section
namespace SevenEighths.ProbeLocal
theorem compensated_phase_error_bound (V W D P B q vInv : ℂ) (T : ℝ)
    (_hT : 0 ≤ T) (hV : ‖V‖ ≤ 1 / 2) (hW : ‖W‖ ≤ 1)
    (hD : ‖D‖ ≤ 1 / 2) (hq : ‖q‖ ≤ 1)
    (hVT : ‖V‖ ≤ T) (hDT : ‖D‖ ≤ T)
    (hE : ‖P + D‖ ≤ 28 * T) (hBE : ‖B‖ * ‖P + D‖ ≤ 28 * T)
    (hv : ‖vInv‖≤1) (hBD : B * D = vInv) (hWq : vInv*W = q) :
    ‖compensatedReplacement V W D P B q + continuedCorrection V W D P*vInv‖ ≤ 720 * T := by
  have h1V : ‖1 - V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have h1W : ‖1 - W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have h1q : ‖vInv - q‖ ≤ 2 := by
    have := norm_sub_le vInv q
    linarith
  have hiV := inv_one_sub_norm_le_two V hV
  have hiD := inv_one_sub_norm_le_two D hD
  have hfac : ‖(1 - V) * (1 - W) / (1 - D)‖ ≤ 8 := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc
      ‖1 - V‖ * ‖1 - W‖ * ‖(1 - D)⁻¹‖ ≤ (2 : ℝ) * 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have hleft : ‖(vInv - q) * (V / (1 - V) - D)‖ ≤ 6 * T := by
    calc
      _ = ‖vInv - q‖ * ‖V / (1 - V) - D‖ := norm_mul _ _
      _ ≤ 2 * (‖V‖ * 2 + ‖D‖) := by
        gcongr
        calc
          _ ≤ ‖V / (1 - V)‖ + ‖D‖ := norm_sub_le _ _
          _ ≤ _ := by rw [div_eq_mul_inv, norm_mul]; gcongr
      _ ≤ 6 * T := by linarith
  have hright : ‖(B + vInv - q) * (P + D)‖ ≤ 84 * T := by
    have hc : ‖B + vInv - q‖ ≤ ‖B‖ + 2 := by
      calc
        _ = ‖B + (vInv - q)‖ := by congr 1; ring
        _ ≤ ‖B‖ + ‖vInv - q‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    calc
      _ = ‖B + vInv - q‖ * ‖P + D‖ := norm_mul _ _
      _ ≤ (‖B‖ + 2) * ‖P + D‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ 84 * T := by nlinarith
  have hid := continued_normalized_cancellation V W D P B q vInv
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD)
    hBD hWq
  rw [hid, norm_mul]
  calc
    _ ≤ 8 * (‖(vInv - q) * (V / (1 - V) - D)‖ + ‖(B + vInv - q) * (P + D)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 720 * T := by linarith

end SevenEighths.ProbeLocal
end

end OAI

end Source1165

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsFirstRegion.lean; sha256: cadf2b87084c5ccad01c0cbc691c9f97a782d07badf9d908630d181ee6804e4f -/
section Source1166
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem unramifiedClosed_first_region_bound (Q : ℝ) (A eta v x w z : ℂ) (eps : ℝ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (heps : 0<eps) (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedClosed Q A eta v x w z-1‖≤240*Q^(-1-min eps (1/50:ℝ)) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let L := Q^(1/100:ℝ)
  let E := Q^(-(109/100:ℝ))
  let T := Q^(-1-min eps (1/50:ℝ))
  have hL1 : 1≤L := Real.one_le_rpow hQ1 (by norm_num)
  have hT : 0≤T := Real.rpow_nonneg hQ0.le _
  have hV : ‖V‖≤Q^(-(51/25:ℝ)) := by
    rw [show V=coordV Q z from rfl,coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖≤Q^(-(11/10:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖≤L :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖≤Q^(-(51/100:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖≤Q^(-eps) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖≤1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb c : ℝ) (ha : 0≤a) (hb : 0≤b)
      (haa : a≤Q^aa) (hbb : b≤Q^bb) (hc : aa+bb≤c) : a*b≤Q^c := by
    calc
      a*b≤Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _≤Q^c := Real.rpow_le_rpow_of_exponent_le hQ1 hc
  have hRL : ‖R‖*L≤E := hprod _ _ _ _ _ (norm_nonneg _) (by positivity) hR le_rfl (by norm_num)
  have hKV : ‖K‖*‖V‖≤E := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by linarith)
  have hRW : ‖R‖*(1+‖W‖)≤2*E := by
    calc
      _≤‖R‖*(2*L) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _≤2*E := by nlinarith
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hPE : ‖P+D‖≤28*E := by
    have hh := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    dsimp only [P]
    nlinarith
  have hEL : E*L≤T := hprod _ _ _ _ _ (by positivity) (by positivity) le_rfl le_rfl
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hWE : (1+‖W‖)*‖P+D‖≤56*T := by
    calc
      _≤(2*L)*(28*E) := mul_le_mul (by linarith) hPE (norm_nonneg _) (by positivity)
      _≤56*T := by nlinarith
  have hDV : ‖D‖*‖V‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hVW : ‖V‖*‖W‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hDW : ‖D‖*‖W‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (coordD_norm_le Q hQ0 eta v x heta hv) (coordW_norm_le Q hQ0 v w hv)
    (by have := min_le_left eps (1/50:ℝ);linarith)
  have hDVW : ‖D‖*‖V‖*‖W‖≤T := by
    calc
      _ = (‖D‖*‖W‖)*‖V‖ := by ring
      _ ≤ ‖D‖*‖W‖ := mul_le_of_le_one_right (by positivity) (by linarith)
      _ ≤ T := hDW
  have hh := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖≤240*T
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI

end Source1166

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsSelectedError.lean; sha256: 93d1ec301f9630f44e8599cf3b90d6187d7cab55b8aa0734a0b6ef8e0be8a483 -/
section Source1167
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

def unramifiedMarked (Q : ℝ) (A eta v x w z : ℂ) : ℂ :=
  markedFactor (coordR Q A x z) (coordV Q z) (Q:ℂ)⁻¹ (coordK Q eta x w)
    (-coordD Q eta v x+coordW Q v w*coordR Q A x z) 1

lemma unramifiedMarked_selected_error (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedMarked Q A eta v x w z+coordD Q eta v x‖≤28 ∧
    ‖star eta*(Q:ℂ)^x‖*‖unramifiedMarked Q A eta v x w z+coordD Q eta v x‖≤28 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  let R := coordR Q A x z
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let B := star eta*(Q:ℂ)^x
  have hR : ‖R‖≤Q^(4-6*x.re-6*z.re) := coordR_norm_le Q hQ0 A x z hA
  have hV : ‖V‖=Q^(-6*z.re) := coordV_norm Q hQ0 z
  have hD : ‖D‖≤Q^(-x.re) := coordD_norm_le Q hQ0 eta v x heta hv
  have hW : ‖W‖≤1 := (coordW_norm_le Q hQ0 v w hv).trans
    (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hK : ‖K‖≤Q^(1-x.re-w.re) := coordK_norm_le Q hQ1 eta x w heta
  have hB : ‖B‖≤Q^x.re := by
    dsimp only [B]
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by linarith))
  have hVh : ‖V‖≤1/2 := by rw [hV];exact rpow_le_half Q _ hQ (by linarith)
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by linarith))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb : ℝ) (ha : 0≤a) (hb : 0≤b)
      (haa : a≤Q^aa) (hbb : b≤Q^bb) (he : aa+bb≤0) : a*b≤1 := by
    calc
      a*b≤Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _≤1 := Real.rpow_le_one_of_one_le_of_nonpos hQ1 he
  have hKV : ‖K‖*‖V‖≤1 := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV.le (by linarith)
  have hBR : ‖B‖*‖R‖≤1 := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hB hR (by linarith)
  have hKV' : ‖K‖*‖V‖≤Q^(1-x.re-w.re-6*z.re) := by
    calc
      _≤Q^(1-x.re-w.re)*Q^(-6*z.re) := mul_le_mul hK hV.le (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
      _=_ := by rw [←Real.rpow_add hQ0];congr 1;ring
  have hBKV : ‖B‖*(‖K‖*‖V‖)≤1 := hprod _ _ _ _ (norm_nonneg _) (by positivity) hB hKV' (by linarith)
  have hE := unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
  change ‖unramifiedMarked Q A eta v x w z+D‖≤_ at hE
  have hE' : ‖unramifiedMarked Q A eta v x w z+D‖≤24*‖R‖+4*(‖K‖*‖V‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg R)]
  constructor
  · change ‖unramifiedMarked Q A eta v x w z+D‖≤28
    linarith
  · have hh := mul_le_mul_of_nonneg_left hE' (norm_nonneg B)
    change ‖B‖*‖unramifiedMarked Q A eta v x w z+D‖≤28
    nlinarith

end SevenEighths.ProbeEuler
end

end OAI

end Source1167

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsSelectedUnramified.lean; sha256: 99172118c423a4e2975b949ddc53b238f8b59645587f7839b5b7e853fac2a087 -/
section Source1168
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

def unramifiedSelected (Q : ℝ) (A eta v x w z : ℂ) : ℂ :=
  compensatedReplacement (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w))

lemma selected_phase_identities (Q : ℝ) (eta v x w : ℂ)
    (hQ : 0<Q) (heta : ‖eta‖=1) (hv : ‖v‖=1) :
    (star eta*(Q:ℂ)^x)*coordD Q eta v x=star v ∧
      star v*coordW Q v w=(Q:ℂ)^(-w) := by
  have hQ0 : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  constructor
  · unfold coordD
    calc
      _=(star eta*eta)*((Q:ℂ)^x*(Q:ℂ)^(-x))*star v := by ring
      _=star v := by rw [PrincipalSlotEstimate.unit_phase_inverse eta heta,←Complex.cpow_add _ _ hQ0];simp
  · unfold coordW
    rw [←mul_assoc,PrincipalSlotEstimate.unit_phase_inverse v hv,one_mul]

lemma unramifiedSelected_error_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v‖≤720 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by linarith)
  have hD : ‖coordD Q eta v x‖≤1/2 :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans (rpow_le_half Q _ hQ (by linarith))
  have hW : ‖coordW Q v w‖≤1 :=
    (coordW_norm_le Q hQ0 v w hv.le).trans (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hq : ‖(Q:ℂ)^(-w)‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  have he := unramifiedMarked_selected_error Q A eta v x w z hQ hA heta.le hv.le hx hw hz
  have hi := selected_phase_identities Q eta v x w hQ0 heta hv
  have hh := compensated_phase_error_bound (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w)) (star v) 1
    (by norm_num) hV hW hD hq (by linarith) (by linarith)
    (by simpa using he.1) (by simpa using he.2) (by rw [norm_star,hv]) hi.1 hi.2
  simpa only [mul_one,unramifiedSelected,unramifiedClosed,unramifiedMarked] using hh

lemma unramifiedSelected_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedSelected Q A eta v x w z‖≤961 := by
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (1/4) hQ hA heta.le hv.le
    (by norm_num) (by linarith) hz (by linarith) (by linarith)
  have hpow : Q^(-1-min (1/4:ℝ) (1/50))≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hH : ‖unramifiedClosed Q A eta v x w z‖≤241 := by
    have hh := norm_add_le (unramifiedClosed Q A eta v x w z-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at hh
    nlinarith
  have he := unramifiedSelected_error_bound Q A eta v x w z hQ hA heta hv hx hw hz
  have hh := norm_sub_le
    (unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v)
    (unramifiedClosed Q A eta v x w z*star v)
  rw [add_sub_cancel_right,norm_mul,norm_star,hv,mul_one] at hh
  linarith

lemma unramifiedSelected_zero (Q : ℝ) (v x w z : ℂ) :
    unramifiedSelected Q 0 0 v x w z= -(Q:ℂ)^(-w)*(1-coordV Q z*coordW Q v w) := by
  simp only [unramifiedSelected,unramifiedMarked,coordR,coordD,coordK,zero_mul,
    neg_zero,add_zero,markedFactor,zero_sub,sub_zero,div_one,mul_zero,
    star_zero,compensatedReplacement]
  ring

lemma unramifiedSelected_zero_bound (Q : ℝ) (v x w z : ℂ)
    (hQ : 4≤Q) (hv : ‖v‖≤1) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedSelected Q 0 0 v x w z‖≤2 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hV : ‖coordV Q z‖≤1 := by
    rw [coordV_norm Q hQ0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  have hW : ‖coordW Q v w‖≤1 :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hq : ‖(Q:ℂ)^(-w)‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  rw [unramifiedSelected_zero,norm_mul,norm_neg]
  have ht := norm_sub_le (1:ℂ) (coordV Q z*coordW Q v w)
  rw [norm_one,norm_mul] at ht
  have hp : ‖coordV Q z‖*‖coordW Q v w‖≤1 := by nlinarith [norm_nonneg (coordV Q z)]
  nlinarith [norm_nonneg (1-coordV Q z*coordW Q v w)]

end SevenEighths.ProbeEuler
end

end OAI

end Source1168

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsSelectedActual.lean; sha256: 4191225d6d759e0c253d8fbc609ba7f3b27979d9be9b47fb633373e4f77c4982 -/
section Source1169
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma elementCoeff_zero_or_norm_one (eta : HeckeFamily.Character) (p : O) :
    HeckeFamily.elementCoeff eta p=0 ∨ ‖HeckeFamily.elementCoeff eta p‖=1 := by
  by_cases h : HeckeFamily.elementCoeff eta p=0
  · exact Or.inl h
  · right
    let : Finite (O ⧸ eta.modulus) := Ring.HasFiniteQuotients.finiteQuotient eta.modulus_ne_bot
    let : Fintype (O ⧸ eta.modulus) := Fintype.ofFinite _
    have hu : IsUnit (Ideal.Quotient.mk eta.modulus p) := eta.residue.apply_ne_zero_iff.mp h
    obtain ⟨u,hu⟩ := hu
    change ‖eta.residue (Ideal.Quotient.mk eta.modulus p)‖=1
    rw [←hu]
    exact FiniteRayExpansion.norm_char_unit eta.residue u

def actualUnramifiedSelected (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (x w z : ℂ) : ℂ :=
  unramifiedSelected (Ideal.absNorm (Ideal.span {p})) (actualAPhase eta p)
    (HeckeFamily.elementCoeff eta p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u)) x w z

theorem actualUnramifiedSelected_bound (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hu : IsCoprime u p)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (x w z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖actualUnramifiedSelected eta p u hg x w z‖≤961 := by
  have hv := Complex.norm_eq_one_of_pow_eq_one (ProbePhysical.actualSextic_unit_six p u hg hc hu) (by decide : (6:ℕ)≠0)
  unfold actualUnramifiedSelected
  rcases elementCoeff_zero_or_norm_one eta p with heta|heta
  · have hA : actualAPhase eta p=0 := by simp [actualAPhase,heta]
    rw [heta,hA]
    exact (unramifiedSelected_zero_bound _ _ x w z hQ hv.le hw hz).trans (by norm_num)
  · exact unramifiedSelected_bound _ _ _ _ x w z hQ (actualAPhase_norm_le_one eta p) heta hv hx hw hz

end SevenEighths.ProbeEuler
end

end OAI

end Source1169

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsSharpScalar.lean; sha256: e18f17ba395bfb991aa22ec942c278ae3a62b21e642080ac0dde703ca9e0b23f -/
section Source1170
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma primeGauss_actual_pow_norm (r : ℕ) (hr : r≠0) (hr6 : r<6) :
    ‖primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^r) 1‖=
      Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn := localGamma_norm_one p hp.ne_zero hg hc r hr hr6
  rw [localGamma,ProbePhase.normalizedTraceGauss_eq_normalizedGauss] at hn
  simp only [ProbeGauss.normalizedGauss,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hcard : (Fintype.card (O ⧸ Ideal.span {p}):ℝ)=Ideal.absNorm (Ideal.span {p}) := by
    rw [←Nat.card_eq_fintype_card];rfl
  rw [hcard] at hn
  have hn' := (div_eq_one_iff_eq (Real.sqrt_pos.mpr hQ).ne').mp hn
  simpa only [primeGauss,tsum_fintype,gaussSum,map_one,one_mul] using hn'

include hc in
lemma nonprincipal_kzero_norm (n j : ℕ) (hn : n<5) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n 0 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^n*Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  rw [positiveScalar_kzero,actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_right (by omega : ¬6∣n+1)]
  split_ifs
  · rw [norm_mul,norm_pow,Complex.norm_natCast,primeGauss_actual_pow_norm p hp hg hc (n+1) (by omega) (by omega)]
  · simp only [norm_zero]
    positivity

include hc in
lemma nonprincipal_kone_norm (n j : ℕ) (hn : 0<n) (hn6 : n<6) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n 1 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1) := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by decide : (1:ℕ)≠0)]
  by_cases hj : 1≤j
  · rw [ite_eq_left ⟨rfl,hj⟩,gaussValuationTable,ite_eq_right (by omega : ¬6∣n)]
    split_ifs
    · rw [norm_mul,norm_mul,norm_inv,
        Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide),inv_one,one_mul,
        primeGauss_actual_norm p hp.ne_zero hg hc,norm_mul,norm_pow,Complex.norm_natCast,
        primeGauss_actual_pow_norm p hp hg hc n (by omega) hn6]
      have hsq := Real.sq_sqrt (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {p})) : (0:ℝ)≤_)
      rw [pow_succ]
      apply le_of_eq
      calc
        _ = (Ideal.absNorm (Ideal.span {p}):ℝ)^n*(Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ))^2 := by ring
        _ = _ := by rw [hsq]
    · simp only [mul_zero,norm_zero]
      positivity
  · rw [ite_eq_right (by omega),norm_zero]
    positivity

include hc in
lemma even_base_kzero_norm (m j : ℕ) (hj : j<6) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 5 0 (j+6*m)‖≤
      if m=0 then (Ideal.absNorm (Ideal.span {p}):ℝ)^5 else (Ideal.absNorm (Ideal.span {p}):ℝ)^6 := by
  have he := row_even_kzero p hp hg hc 0 m j hj
  norm_num only [Nat.mul_zero,zero_add] at he
  rw [he]
  by_cases hm : m=0
  · subst m
    norm_num only [Nat.reduceLeDiff,ite_false,ite_true,and_true]
    split_ifs <;> simp [norm_pow]
  · rw [ite_eq_left (by omega),ite_eq_right hm,norm_mul,norm_pow,Complex.norm_natCast]
    have hQ1 : (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
      have hh := SmoothMobiusCorrection.prime_norm_two_le
        ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩
      change 2≤Ideal.absNorm (Ideal.span {p}) at hh
      exact_mod_cast (by omega : 1≤Ideal.absNorm (Ideal.span {p}))
    have hsub : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)-1‖=(Ideal.absNorm (Ideal.span {p}):ℝ)-1 := by
      rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    rw [hsub,show (Ideal.absNorm (Ideal.span {p}):ℝ)^6=(Ideal.absNorm (Ideal.span {p}):ℝ)^5*(Ideal.absNorm (Ideal.span {p}):ℝ) by ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

include hc in
lemma even_base_kone_zero (j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 5 1 j=0 := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by decide : (1:ℕ)≠0)]
  by_cases hj1 : 1≤j
  · rw [ite_eq_left ⟨rfl,hj1⟩,gaussValuationTable,ite_eq_right (by decide : ¬6∣5),
      ite_eq_right (by omega : j-1≠5),mul_zero]
  · rw [ite_eq_right (by omega)]

end SevenEighths.ProbePrimePower
end

end OAI

end Source1170

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsFirstTerms.lean; sha256: 33f3a648d2262942af8c3e4423314650c9e37172b552677da6ca48a888595bee -/
section Source1171
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma pow_mul_sqrt (Q : ℝ) (hQ : 0<Q) (n : ℕ) : Q^n*Real.sqrt Q=Q^((n:ℝ)+1/2) := by
  rw [Real.rpow_add hQ,Real.rpow_natCast,Real.sqrt_eq_rpow]

include hc in
lemma sourceRowTerm_norm_from_scalar (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (nu : ℝ)
    (hs : ‖sourceScalar p hp hg (e+3*l) k (j+6*m)‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)
    (he : nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)≤0) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2 := by
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hrho := Complex.norm_eq_one_of_pow_eq_one hρ (by decide : (6:ℕ)≠0)
  rw [sourceRowTerm,norm_mul,norm_div,norm_pow,norm_pow,hrho,one_pow,one_pow,div_self (by norm_num : (1:ℝ)≠0),one_mul]
  apply (sourceWeightedScalar_norm_le _ hQ eta a _ _ _ x w z _ heta ha
    (localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide))
    (by rw [norm_star];exact localGamma_norm_one p hp.ne_zero hg hc 3 (by decide) (by decide))
    (Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide)) e l k m).trans
  calc
    _ ≤ (2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)*
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = 2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) := by
      rw [mul_assoc,←Real.rpow_add hQ]
      congr 2
      ring
    _ ≤ 2 := by
      have hh := Real.rpow_le_one_of_one_le_of_nonpos (show (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) by linarith) he
      linarith

include hc in
theorem sourceRowTerm_first_base (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (_hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1≤x.re+w.re) (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2 := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ : 0<Q := by
    dsimp only [Q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hm0 : (0:ℝ)≤m := Nat.cast_nonneg m
  have hzm : 0≤6*z.re*(m:ℝ) := by positivity
  have hzm1 (hm : m≠0) : 6*z.re≤6*z.re*(m:ℝ) := by
    have hm1 : (1:ℝ)≤m := by exact_mod_cast (by omega : 1≤m)
    nlinarith
  have hrelax (v : ℝ) : Q^v≤2*Q^v := by nlinarith [Real.rpow_nonneg hQ.le v]
  have hz0 (t k : ℕ) (ht : t≠0) : sourceScalar p hp hg t k (j+6*m)=
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (t-1) k (j+6*m) := by
    rw [sourceScalar,ite_eq_right ht]
  rcases hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · by_cases hm : m=0
      · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 5
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_left hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^5≤2*Q^5 by nlinarith [pow_nonneg hQ.le 5])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          linarith
      · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 6
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_right hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
    · by_cases hm : m=0
      · subst m
        simp only [sourceRowTerm,sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,
          Nat.reduceEqDiff,ite_false,mul_zero,add_zero,even_base_kone_zero p hp hg hc j hj,
          sourceWeightedScalar,zero_mul,mul_zero,norm_zero]
        norm_num
      · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 2 1 m 6
        · have hs := nonprincipal_kone_norm p hp hg hc 5 (j+6*m) (by decide) (by decide)
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 1 0 0 m (1/2)
      · have hs := nonprincipal_kzero_norm p hp hg hc 0 (j+6*m) (by decide)
        simp only [pow_zero,one_mul,Real.sqrt_eq_rpow] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 0 (by decide),Nat.reduceSub] using hs.trans (hrelax (1/2))
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 1 0 1 m (3/2)
      · have hs := positiveScalar_norm_le p hp hg hc 0 1 (j+6*m) (by decide)
        simp only [Nat.zero_add,pow_one] at hs
        have he : 2*Q*Real.sqrt Q=2*Q^(3/2:ℝ) := by
          have ht := pow_mul_sqrt Q hQ 1
          norm_num at ht
          rw [mul_assoc,ht]
        rw [he] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 1 (by decide),Nat.reduceSub] using hs
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 1 0 m (5/2)
      · have hs := nonprincipal_kzero_norm p hp hg hc 2 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (5/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 1 1 m 3
      · have hs := nonprincipal_kone_norm p hp hg hc 2 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 3 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^3≤2*Q^3 by nlinarith [pow_nonneg hQ.le 3])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 1 1 0 m (7/2)
      · have hs := nonprincipal_kzero_norm p hp hg hc 3 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (7/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 1 1 1 m 4
      · have hs := nonprincipal_kone_norm p hp hg hc 3 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 4 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^4≤2*Q^4 by nlinarith [pow_nonneg hQ.le 4])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith

end SevenEighths.ProbeEuler
end

end OAI

end Source1171

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsFirstRamified.lean; sha256: 761c1527e0cbe2807acac9e27b012211a97edf08c842fd2330e0e6b8e74f78b6 -/
section Source1172
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma first_region_V_half (Q : ℝ) (hQ : 4≤Q) (z : ℂ) (hz : (17/50:ℝ)≤z.re) :
    ‖coordV Q z‖≤1/2 := by
  rw [coordV_norm Q (by linarith)]
  exact rpow_le_half Q _ hQ (by linarith)

lemma first_region_R_half (Q : ℝ) (hQ : 4≤Q) (a x z : ℂ) (ha : ‖a‖≤1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) :
    ‖evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z)‖≤1/2 := by
  rw [evenRatio_eq_coordR Q (by linarith)]
  apply (coordR_norm_le Q (by linarith) (a^2) x z (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha)).trans
  exact rpow_le_half Q _ hQ (by linarith)

include hc in
lemma rowBaseFinite_first_region (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1≤x.re+w.re) (j e l : ℕ) (hj : j<6)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖rowBaseFinite p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l‖≤16 := by
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_V_half _ hQ z hz)
  have ht' (k : Fin 2) (m : ℕ) :
      ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        rho j e l k.val m‖≤2 := by
    have ht : e+3*l≠0 := by rcases hf with h|h|h|h <;> omega
    rw [←sourceRowTerm_pos p hp hg eta a rho x w z j e l k.val m ht]
    exact sourceRowTerm_first_base p hp hg hc eta a rho x w z heta ha hρ hx hw hz hxw
      j e l k.val m hj (by omega) hf
  unfold rowBaseFinite
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : Fin 2,(8:ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_add_le _ _).trans
      have hab := (norm_add_le _ _).trans (add_le_add (ht' k 0) (ht' k 1))
      have hd : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
          rho j e l k.val 2/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)‖≤4 := by
        rw [div_eq_mul_inv,norm_mul]
        exact (mul_le_mul (ht' k 2) hv (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
      linarith
    _ = _ := by norm_num

include hc in
theorem rowClosedMarked_first_region (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) (hxw : 1≤x.re+w.re) (j : ℕ) (hj : j<6) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤128 := by
  have h02 := rowBaseFinite_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j 0 2 hj (by omega)
  have h10 := rowBaseFinite_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j 1 0 hj (by omega)
  have h01 := rowBaseFinite_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j 0 1 hj (by omega)
  have h11 := rowBaseFinite_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j 1 1 hj (by omega)
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha hx hz)
  simp only [Complex.ofReal_natCast] at hr
  unfold rowClosedMarked
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  nlinarith

include hc in
theorem ramifiedClosed_first_region_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) (hxw : 1≤x.re+w.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedClosed p hp hg eta a rho x w z j‖≤193 := by
  have hb := rowClosedMarked_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j hj
  have hv := first_region_V_half _ hQ z hz
  have hs := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
  simp only [norm_one] at hs
  unfold ramifiedClosed
  apply (norm_add_le _ _).trans
  rw [norm_one,norm_mul]
  have hm := mul_le_mul (show ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 by linarith)
    hb (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)
  linarith

end SevenEighths.ProbeEuler
end

end OAI

end Source1172

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsSelectedTerms.lean; sha256: afe6f02b31c606603f877cd12146ce8c7f73ffe2b97d24f47e41a2619c22ab39 -/
section Source1173
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma sourceRowTerm_norm_from_scalar_power (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (nu B : ℝ)
    (hs : ‖sourceScalar p hp hg (e+3*l) k (j+6*m)‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)
    (he : nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)≤B) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^B := by
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hrho := Complex.norm_eq_one_of_pow_eq_one hρ (by decide : (6:ℕ)≠0)
  rw [sourceRowTerm,norm_mul,norm_div,norm_pow,norm_pow,hrho,one_pow,one_pow,div_self (by norm_num : (1:ℝ)≠0),one_mul]
  apply (sourceWeightedScalar_norm_le _ hQ eta a _ _ _ x w z _ heta ha
    (localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide))
    (by rw [norm_star];exact localGamma_norm_one p hp.ne_zero hg hc 3 (by decide) (by decide))
    (Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide)) e l k m).trans
  calc
    _ ≤ (2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)*
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = 2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) := by
      rw [mul_assoc,←Real.rpow_add hQ]
      congr 2
      ring
    _ ≤ 2*(Ideal.absNorm (Ideal.span {p}):ℝ)^B := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) by linarith) he

include hc in
theorem sourceRowTerm_selected_base (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (_hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ : 0<Q := by
    dsimp only [Q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hm0 : (0:ℝ)≤m := Nat.cast_nonneg m
  have hb0 : (0:ℝ)≤max (1-w.re) 0 := le_max_right _ _
  have hb1 : 1-w.re≤max (1-w.re) 0 := le_max_left _ _
  have hzm : 0≤6*z.re*(m:ℝ) := by positivity
  have hzm1 (hm : m≠0) : 6*z.re≤6*z.re*(m:ℝ) := by
    have hm1 : (1:ℝ)≤m := by exact_mod_cast (by omega : 1≤m)
    nlinarith
  have hrelax (v : ℝ) : Q^v≤2*Q^v := by nlinarith [Real.rpow_nonneg hQ.le v]
  have hz0 (t k : ℕ) (ht : t≠0) : sourceScalar p hp hg t k (j+6*m)=
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (t-1) k (j+6*m) := by
    rw [sourceScalar,ite_eq_right ht]
  rcases hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · by_cases hm : m=0
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 5 (-x.re+max (1-w.re) 0)
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_left hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^5≤2*Q^5 by nlinarith [pow_nonneg hQ.le 5])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          linarith
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 6 (-x.re+max (1-w.re) 0)
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_right hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
    · by_cases hm : m=0
      · subst m
        simp only [sourceRowTerm,sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,
          Nat.reduceEqDiff,ite_false,mul_zero,add_zero,even_base_kone_zero p hp hg hc j hj,
          sourceWeightedScalar,zero_mul,mul_zero,norm_zero]
        positivity
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 1 m 6 (-x.re+max (1-w.re) 0)
        · have hs := nonprincipal_kone_norm p hp hg hc 5 (j+6*m) (by decide) (by decide)
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 0 m (1/2) (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kzero_norm p hp hg hc 0 (j+6*m) (by decide)
        simp only [pow_zero,one_mul,Real.sqrt_eq_rpow] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 0 (by decide),Nat.reduceSub] using hs.trans (hrelax (1/2))
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 1 m (3/2) (-x.re+max (1-w.re) 0)
      · have hs := positiveScalar_norm_le p hp hg hc 0 1 (j+6*m) (by decide)
        simp only [Nat.zero_add,pow_one] at hs
        have he : 2*Q*Real.sqrt Q=2*Q^(3/2:ℝ) := by
          have ht := pow_mul_sqrt Q hQ 1
          norm_num at ht
          rw [mul_assoc,ht]
        rw [he] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 1 (by decide),Nat.reduceSub] using hs
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 0 m (5/2) (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kzero_norm p hp hg hc 2 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (5/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 1 m 3 (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kone_norm p hp hg hc 2 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 3 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^3≤2*Q^3 by nlinarith [pow_nonneg hQ.le 3])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 0 m (7/2) (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kzero_norm p hp hg hc 3 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (7/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 1 m 4 (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kone_norm p hp hg hc 3 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 4 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^4≤2*Q^4 by nlinarith [pow_nonneg hQ.le 4])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith

end SevenEighths.ProbeEuler
end

end OAI

end Source1173

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsSelectedBound.lean; sha256: 0441eff7953b701e40123f25aa890fc9388166f7e76a7f138b14b88b214563cb -/
section Source1174
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma rowBaseFinite_selected_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (j e l : ℕ) (hj : j<6)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖rowBaseFinite p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l‖≤16*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  have hpow : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by positivity
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_V_half _ hQ z hz)
  have ht' (k : Fin 2) (m : ℕ) :
      ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        rho j e l k.val m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
    have ht : e+3*l≠0 := by rcases hf with h|h|h|h <;> omega
    rw [←sourceRowTerm_pos p hp hg eta a rho x w z j e l k.val m ht]
    exact sourceRowTerm_selected_base p hp hg hc eta a rho x w z heta ha hρ hx hw hz
      j e l k.val m hj (by omega) hf
  unfold rowBaseFinite
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : Fin 2,8*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_add_le _ _).trans
      have hab := (norm_add_le _ _).trans (add_le_add (ht' k 0) (ht' k 1))
      have hd : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
          rho j e l k.val 2/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)‖≤4*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
        rw [div_eq_mul_inv,norm_mul]
        exact (mul_le_mul (ht' k 2) hv (norm_nonneg _) (by positivity)).trans_eq (by ring)
      linarith
    _ = _ := by simp;ring

include hc in
theorem rowClosedMarked_selected_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j<6) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤128*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  have hpow : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by positivity
  have h02 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 2 hj (by omega)
  have h10 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 0 hj (by omega)
  have h01 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 1 hj (by omega)
  have h11 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 1 hj (by omega)
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha (by linarith) hz)
  simp only [Complex.ofReal_natCast] at hr
  unfold rowClosedMarked
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI

end Source1174

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsSelectedRamified.lean; sha256: 6a12233fc2e5cfbe665021090709bb4b16e051e8f6e2d0ca6cb299c265277e1b -/
section Source1175
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedSelected (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j -
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)*ramifiedClosed p hp hg eta a rho x w z j

lemma ramifiedSelected_eq_replacement (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedSelected p hp hg eta a rho x w z j =
      ProbeLocal.compensatedReplacement (coordV (Ideal.absNorm (Ideal.span {p})) z) 0 0
        (rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j)
        (star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) := by
  rw [ProbeLocal.continued_ramified_compensation]
  simp only [ramifiedSelected,ramifiedClosed,ProbeLocal.continuedCorrection,mul_zero,sub_zero,mul_one,div_one]

include hc in
theorem ramifiedSelected_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x w z j‖≤385*(Ideal.absNorm (Ideal.span {p}):ℝ)^(max (1-w.re) 0) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  let B : ℝ := max (1-w.re) 0
  have hQ0 : 0<Q := by dsimp [Q];linarith
  have hQ1 : 1≤Q := by dsimp [Q];linarith
  have hB0 : 0≤B := le_max_right _ _
  have hM := rowClosedMarked_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j hj
  have hH := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z hQ heta ha hρ
    (by linarith) (by linarith) hz (by linarith) j hj
  have hV := first_region_V_half _ hQ z hz
  have h1V : ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 := by
    have hh := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
    simp only [norm_one] at hh
    linarith
  have hphase : ‖star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x‖≤Q^x.re := by
    change ‖star eta*(Q:ℂ)^x‖≤Q^x.re
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hq : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)‖≤Q^B := by
    change ‖(Q:ℂ)^(-w)‖≤Q^B
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by dsimp [B];linarith)
  have he : Q^x.re*Q^(-x.re+B)=Q^B := by rw [←Real.rpow_add hQ0];congr 1;ring
  unfold ramifiedSelected
  apply (norm_sub_le _ _).trans
  simp only [norm_mul] at hphase ⊢
  calc
    _ ≤ (Q^x.re*(3/2))*(128*Q^(-x.re+B))+Q^B*193 := by
      gcongr
    _ = 385*Q^B := by nlinarith [he]

include hc in
theorem ramifiedSelected_small_bound (eta a rho x z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (t : ℝ) (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x ((1/2:ℂ)+t*Complex.I) z j‖≤
      385*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) := by
  have hh := ramifiedSelected_bound p hp hg hc eta a rho x ((1/2:ℂ)+t*Complex.I) z hQ heta ha hρ hx
    (by norm_num [Complex.mul_re]) hz j hj
  norm_num [Complex.mul_re] at hh ⊢
  exact hh

include hc in
theorem ramifiedSelected_large_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : 1≤w.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x w z j‖≤385 := by
  have hh := ramifiedSelected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx (by linarith) hz j hj
  simpa only [max_eq_right (by linarith : 1-w.re≤0),Real.rpow_zero,mul_one] using hh

end SevenEighths.ProbeEuler
end

end OAI

end Source1175

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/Selected.lean; sha256: 221e743460b517bf875aec1988a8717ad933a3acea47c7a8769fb0fa5ea06f7c -/
section Source1176
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def continuedCompensatedLocal (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z B q : ℂ) : ℂ :=
  ProbeLocal.compensatedReplacement (coordV P.val.absNorm z)
    (coordW P.val.absNorm (idealRowHom u.val P.val) w)
    (coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x)
    (continuedMarkedLocal η u P hs x w z) B q

theorem localNormalization_coordinates (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) :
    localNormalization η u P x w z=
      (1-coordV P.val.absNorm z)*(1-coordW P.val.absNorm (idealRowHom u.val P.val) w)/
        (1-coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x) := by
  unfold localNormalization coordV coordW coordD CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false,Complex.ofReal_natCast]
  rw [show -(6*z)=(-6:ℂ)*z by ring]
  rfl

theorem row_phase_ramified (u : FreeRow) (P : PrimeIdeal) (hP : P.val∣Ideal.span {u.val}) :
    idealRowHom u.val P.val=0 := by
  have hu : u.val∈P.val := (Ideal.dvd_iff_le.mp hP) (Ideal.subset_span (by simp))
  exact idealRowHom_zero_of_dvd u.val P.property (dvd_refl _) hu

theorem continuedCompensatedLocal_ramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    let p := primaryGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    letI : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hg := (supported_prime_data p hp ((span_primaryGenerator_of_supported P.val hs).symm ▸ hs)).1
    continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))=
      ramifiedSelected p hp hg (targetMonoid η p) (actualACube η p)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
        x w z (multiplicity p u.val) := by
  dsimp only
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have he := ramifiedSelected_eq_replacement p hp hg.1 (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val)
  rw [he]
  unfold continuedCompensatedLocal
  rw [row_phase_ramified u P hP]
  simp only [coordW,coordD,zero_mul,mul_zero,star_zero]
  rw [←targetMonoid_primaryGenerator η P.val hs]
  unfold continuedMarkedLocal
  simp only [hspan]
  rfl

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1176

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/SelectedUnramified.lean; sha256: 77e1db98265a3aba0b6f6b46516b2cb14caf1255b56622197dbbef0ccb34300f -/
section Source1177
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem continuedMarkedLocal_unramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1) :
    continuedMarkedLocal η u P hs x w z=
      unramifiedMarked P.val.absNorm (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) (idealRowHom u.val P.val) x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hnot : ¬p∣u.val := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hj := multiplicity_eq_zero_of_not_dvd hnot
  have hb : unitPart u p hp=u.val := by
    have he := (unitPart_spec u p hp).1
    rw [hj,pow_zero,one_mul] at he
    exact he.symm
  have hu : IsCoprime u.val p := by rw [←hb]; exact unitPart_coprime u p hp
  have hρ := actualSextic_unit_six p u.val hg.1 hg.2 hu
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) :=
    HeckeDyadic.norm_pos ⟨Ideal.span {p},Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero⟩
  have hr := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (actualACube η p) x z
  simp only [Complex.ofReal_natCast] at hr
  have hR' : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hr,actualACube_sq,hspan]
    exact hR
  have hv' : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by rw [hspan];exact hV
  have hh := rowClosedMarked_unramified p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p)
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) _ hρ hv' hR'
  have hk := coordK_eq_geometric (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (targetMonoid η p) x w
  simp only [Complex.ofReal_natCast] at hk
  have hi : (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val))⁻¹=
      star (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val)) :=
    Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hρ (by decide))
  have heta : idealCoeff η P.val=targetMonoid η p :=
    (targetMonoid_primaryGenerator η P.val hs).symm
  have hphase : idealRowHom u.val P.val=
      actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    conv_lhs => rw [←hspan]
    exact idealRowHom_prime u.val (Ideal.span {p}) hg.1
  simp only [hspan] at hh hr hk
  unfold continuedMarkedLocal
  change rowClosedMarked p hp hg.1 (targetMonoid η p) (actualACube η p)
    ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) (multiplicity p u.val)=_
  rw [hj,hb,hh,hr,←hk,actualACube_sq,heta,hphase]
  simp only [unramifiedMarked,coordD,coordW,div_eq_mul_inv,hi,Complex.ofReal_natCast]
  congr 1; ring

theorem continuedCompensatedLocal_unramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1) :
    continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))=
      unramifiedSelected P.val.absNorm (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) (idealRowHom u.val P.val) x w z := by
  rw [continuedCompensatedLocal,continuedMarkedLocal_unramified η u P hs hn x w z hV hR]
  rfl

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1177

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/SelectedAgreement.lean; sha256: 4fa9badab209da472ae006324f82d9156baa6f2e826cdd6a72c0607aa0683785 -/
section Source1178
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def finiteLocalCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  ProbeLocal.continuedCorrection (coordV P.val.absNorm z)
    (coordW P.val.absNorm (idealRowHom u.val P.val) w)
    (coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x)
    (continuedMarkedLocal η u P hs x w z)

theorem continuedCompensatedLocal_eq_difference (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z B q : ℂ) :
    continuedCompensatedLocal η u P hs x w z B q=
      B*continuedMarkedLocal η u P hs x w z*localNormalization η u P x w z-
        q*finiteLocalCorrection η u P hs x w z := by
  rw [localNormalization_coordinates]
  unfold continuedCompensatedLocal finiteLocalCorrection ProbeLocal.compensatedReplacement ProbeLocal.continuedCorrection
  ring

theorem ramifiedCorrection_eq_marked (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    ramifiedCorrection η u P hs x w z=
      1+(1-coordV P.val.absNorm z)*continuedMarkedLocal η u P hs x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := (supported_prime_data p hp hsp).1
  have hnorm : Ideal.absNorm (Ideal.span {p})=P.val.absNorm := congrArg Ideal.absNorm hspan
  change ramifiedClosed p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val)=
    1+(1-coordV P.val.absNorm z)*rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
      ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) (multiplicity p u.val)
  unfold ramifiedClosed
  rw [hnorm]

theorem finiteLocalCorrection_ramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    finiteLocalCorrection η u P hs x w z=ramifiedCorrection η u P hs x w z := by
  rw [ramifiedCorrection_eq_marked]
  unfold finiteLocalCorrection
  rw [row_phase_ramified u P hP]
  simp only [coordW,coordD,star_zero,mul_zero,zero_mul,ProbeLocal.continuedCorrection,
    sub_zero,mul_one,div_one]

theorem finiteLocalCorrection_unramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1) :
    finiteLocalCorrection η u P hs x w z=idealUnramifiedCorrection η u P x w z := by
  rw [finiteLocalCorrection,continuedMarkedLocal_unramified η u P hs hn x w z hV hR]
  rfl

theorem initial_marked_geometry (η : Character) (P : PrimeIdeal) (x z : ℂ)
    (hx : 3/2<x.re) (hz : 1/6<z.re) :
    ‖coordV P.val.absNorm z‖<1 ∧
      ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1 := by
  have hQ : (1:ℝ)<P.val.absNorm := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1:ℕ)<2) (SmoothMobiusCorrection.prime_norm_two_le P))
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  constructor
  · rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  · apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η _)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)

theorem finiteLocalCorrection_eq_initial (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    finiteLocalCorrection η u P hs x w z=localCorrection η u P x w z := by
  by_cases hP : P.val∣Ideal.span {u.val}
  · rw [finiteLocalCorrection_ramified η u P hs hP]
    exact (localCorrection_eq_ramified η u P hs hP x w z hx hw hz).symm
  · have hg := initial_marked_geometry η P x z hx hz
    rw [finiteLocalCorrection_unramified η u P hs hP x w z hg.1 hg.2]
    exact (localCorrection_unramified_ideal η u P hs (supported_prime_coprime P hs u.val hP)
      x w z hx hw hz).symm

theorem continuedCompensatedLocal_eq_initial (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z B q : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedCompensatedLocal η u P hs x w z B q=compensatedLocalCorrection η u P x w z B q := by
  rw [continuedCompensatedLocal_eq_difference,
    continuedMarkedLocal_eq_initial η u P hs x w z hx hw hz,
    finiteLocalCorrection_eq_initial η u P hs x w z hx hw hz]
  unfold compensatedLocalCorrection markedLocalCorrection
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1178

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/FirstTail.lean; sha256: 6bdd82394b7156566a7413444aa3d5188dd0df400f8cbe3e662d980de0d1035d -/
section Source1179
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
local notation "O" => HeckeFamily.O

def firstPrimeDefectBound (eps : ℝ) (P : PrimeIdeal) : ℝ :=
  240*(P.val.absNorm : ℝ)^(-1-min eps (1/50:ℝ))

theorem firstPrimeDefectBound_nonneg (eps : ℝ) (P : PrimeIdeal) :
    0≤firstPrimeDefectBound eps P := by unfold firstPrimeDefectBound; positivity

theorem firstPrimeDefectBound_summable (eps : ℝ) (heps : 0<eps) :
    Summable (firstPrimeDefectBound eps) := by
  have ht : 1<(1+min eps (1/50:ℝ) : ℂ).re := by
    simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re]
    have hm : 0<min eps (1/50:ℝ) := lt_min heps (by norm_num)
    linarith
  have h := (CubicEisenstein.fullIdealWeight_summable_norm
    (1+min eps (1/50:ℝ) : ℂ) ht).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*‖CubicEisenstein.fullIdealWeight (1+min eps (1/50:ℝ) : ℂ) P.val‖=_
  unfold firstPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  simp only [Complex.neg_re,Complex.add_re,Complex.one_re,Complex.ofReal_re]
  congr 2
  ring

structure FirstTail (eps : ℝ) (S : Finset (Ideal O)) : Prop where
  positive : 0<eps
  norm_four : ∀P : PrimeIdeal,P.val∉S → 4≤P.val.absNorm
  small : (∑' P : {P : PrimeIdeal // P.val∉S},firstPrimeDefectBound eps P.val)≤1/6

theorem FirstTail.summable {eps : ℝ} {S : Finset (Ideal O)} (h : FirstTail eps S) :
    Summable (fun P : {P : PrimeIdeal // P.val∉S}=>firstPrimeDefectBound eps P.val) :=
  (firstPrimeDefectBound_summable eps h.positive).subtype _

theorem FirstTail.half {eps : ℝ} {S : Finset (Ideal O)} (h : FirstTail eps S)
    (P : {P : PrimeIdeal // P.val∉S}) : firstPrimeDefectBound eps P.val≤1/2 := by
  have hh := Summable.le_tsum h.summable P (fun Q _=>firstPrimeDefectBound_nonneg eps Q.val)
  linarith [h.small]

theorem exists_first_cutoff (eps : ℝ) (heps : 0<eps) :
    ∃N : ℕ,4≤N ∧ ∀S : Finset (Ideal O),
      (∀P : PrimeIdeal,P.val.absNorm≤N → P.val∈S) → FirstTail eps S := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero (firstPrimeDefectBound eps))).2
    (1/6) (by norm_num)
  obtain ⟨F,hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P=>P.val.absNorm))
  refine ⟨N,le_max_left _ _,?_⟩
  intro S hS
  let T := {P : PrimeIdeal // P.val∉S}
  have hnot (P : T) : P.val∉F := by
    intro hm
    exact P.property (hS P.val ((Finset.le_sup (f:=fun P : PrimeIdeal=>P.val.absNorm) hm).trans
      (le_max_right _ _)))
  let inc : T→{P : PrimeIdeal // P∉F} := fun P=>⟨P.val,hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun P : {P : PrimeIdeal // P∉F}=>P.val) h)
  refine ⟨heps,?_,?_⟩
  · intro P hP
    have hn : ¬P.val.absNorm≤N := fun hn=>hP (hS P hn)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
  · apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _=>firstPrimeDefectBound_nonneg eps P.val) (fun _=>le_rfl)
      ((firstPrimeDefectBound_summable eps heps).subtype _)
      ((firstPrimeDefectBound_summable eps heps).subtype _)

theorem exists_both_source_exclusions (eps : ℝ) (heps : 0<eps)
    (S₀ : Finset (Ideal O)) (hp : ∀P∈S₀,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S₀) :
    ∃S : Finset (Ideal O),S₀⊆S ∧ SourceExclusions S ∧ FirstTail eps S := by
  obtain ⟨N₁,hN₁,hcut₁⟩ := exists_uniform_global_cutoff
  obtain ⟨N₂,hN₂,hcut₂⟩ := exists_first_cutoff eps heps
  let N := max N₁ N₂
  let S := S₀∪smallPrimeSet N
  have hpS : ∀P∈S,Prime P := by
    intro P hP
    rcases Finset.mem_union.mp hP with hP|hP
    · exact hp P hP
    · exact (Finset.mem_filter.mp hP).2
  have hcut : ∀P : PrimeIdeal,P.val.absNorm≤N → P.val∈S := by
    intro P hP
    exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)
  refine ⟨S,Finset.subset_union_left,⟨hpS,hbad.trans Finset.subset_union_left,?_⟩,?_⟩
  · exact hcut₁ S (fun P hP=>hcut P (hP.trans (le_max_left _ _)))
  · exact hcut₂ S (fun P hP=>hcut P (hP.trans (le_max_right _ _)))

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1179

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/FirstProduct.lean; sha256: 36590e3e214dde13bfd4f9016dc480732387be3c4bda7c246f8e562210bebeaf -/
section Source1180
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

theorem unramifiedFactor_first_defect (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hP : 4≤P.val.absNorm) (x w z : ℂ) (eps : ℝ) (heps : 0<eps)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedFactor η u P x w z-1‖≤firstPrimeDefectBound eps P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using firstPrimeDefectBound_nonneg eps P
  · apply unramifiedClosed_first_region_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact heps
    · exact hx
    · exact hz
    · exact hw
    · exact hxw

theorem unramifiedProduct_first_defect (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedProduct S η u x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P => unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw hxw) hS.half hS.small

theorem unramifiedProduct_first_multipliable (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>unramifiedFactor η u P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>unramifiedFactor η u P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>firstPrimeDefectBound eps P.val
  have hB (P) : ‖F P-1‖≤B P :=
    unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw hxw
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1180

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsFirstHolomorphic.lean; sha256: 3d64cf8bc5a0e60cab067939bc54b10a4bd7cd50760b99d6d5a52b4890ba8e98 -/
section Source1181
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma first_open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 1/2≤x.re) (hz : 1/3≤z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem unramifiedClosed_first_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 1/3≤z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedClosed Q A eta v x w z) {x : ℂ|1/2<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := first_open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_first_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 1/2≤x.re) (hz : 1/3≤z.re) :
    AnalyticOnNhd ℂ (fun w=>unramifiedClosed Q A eta v x w z) (Set.univ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro w hw
  have hd := first_open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_first_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : 1/2≤x.re) :
    AnalyticOnNhd ℂ (fun z=>unramifiedClosed Q A eta v x w z) {z : ℂ|1/3<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := first_open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p})

lemma ramifiedClosed_first_analytic_x (eta a rho w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hz : (1/3:ℝ)≤z.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun x=>ramifiedClosed p hp hg eta a rho x w z j) {x : ℂ|1/2<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := first_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx.le hz
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho id (fun _=>w) (fun _=>z) x
    differentiableAt_id (differentiableAt_const w) (differentiableAt_const z) hd.2.1 hd.1 j).differentiableWithinAt

lemma ramifiedClosed_first_analytic_w (eta a rho x z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1)
    (hx : (1/2:ℝ)≤x.re) (hz : (1/3:ℝ)≤z.re) (j : ℕ) :
    Differentiable ℂ (fun w=>ramifiedClosed p hp hg eta a rho x w z j) := by
  intro w
  have hd := first_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz
  exact ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) id (fun _=>z) w
    (differentiableAt_const x) differentiableAt_id (differentiableAt_const z) hd.2.1 hd.1 j

lemma ramifiedClosed_first_analytic_z (eta a rho x w : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hx : (1/2:ℝ)≤x.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun z=>ramifiedClosed p hp hg eta a rho x w z j) {z : ℂ|1/3<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := first_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz.le
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) (fun _=>w) id z
    (differentiableAt_const x) (differentiableAt_const w) differentiableAt_id hd.2.1 hd.1 j).differentiableWithinAt

end SevenEighths.ProbeEuler
end

end OAI

end Source1181

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/FirstAnalytic.lean; sha256: 9adea125a5b73448e9f5c140691e7c99ca2e3f51dba25f3daaadce0c4177c20c -/
section Source1182
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

theorem unramifiedProduct_first_analytic_x (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (w z : ℂ)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedProduct S η u x w z)
      {x : ℂ | max (51/100:ℝ) (1+eps-w.re)<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply (unramifiedClosed_first_analytic_x _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro x hx
      change max (51/100:ℝ) (1+eps-w.re)<x.re at hx
      have hx' := (lt_of_le_of_lt (le_max_left (51/100:ℝ) (1+eps-w.re)) hx)
      change (1/2:ℝ)<x.re
      linarith
  · intro P x hx
    have hx' := (lt_of_le_of_lt (le_max_left (51/100:ℝ) (1+eps-w.re)) hx)
    have hxw := (lt_of_le_of_lt (le_max_right (51/100:ℝ) (1+eps-w.re)) hx)
    exact unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx'.le hz hw (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_analytic_w (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w=>unramifiedProduct S η u x w z)
      {w : ℂ | max (-(1/100:ℝ)) (1+eps-x.re)<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      exact (unramifiedClosed_first_analytic_w _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith) (by linarith)).mono
          (Set.subset_univ _)
  · intro P w hw
    have hw' := (lt_of_le_of_lt (le_max_left (-(1/100:ℝ)) (1+eps-x.re)) hw)
    have hxw := (lt_of_le_of_lt (le_max_right (-(1/100:ℝ)) (1+eps-x.re)) hw)
    exact unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw'.le (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_analytic_z (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    AnalyticOnNhd ℂ (fun z=>unramifiedProduct S η u x w z) {z : ℂ | (17/50:ℝ)<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ=>if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [ite_eq_right h]
      apply (unramifiedClosed_first_analytic_z _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro z hz
      change (17/50:ℝ)<z.re at hz
      change (1/3:ℝ)<z.re
      linarith
  · intro P z hz
    exact unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz.le hw hxw
  · exact hS.half

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1182

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/FirstContinuation.lean; sha256: f3c30b77cfc2cd3221c34dc6da38b954d5a048a596a3bcbd0c0277e3e5a7d686 -/
section Source1183
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem ramifiedCorrection_first_analytic_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (w z : ℂ) (hz : (1/3 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>ramifiedCorrection η u P hs x w z) {x : ℂ | 1/2<x.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_first_analytic_x
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hz

theorem ramifiedCorrection_first_analytic_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (1/2 : ℝ)≤x.re) (hz : (1/3 : ℝ)≤z.re) :
    Differentiable ℂ (fun w =>ramifiedCorrection η u P hs x w z) := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_first_analytic_w
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx
  · exact hz

theorem ramifiedCorrection_first_analytic_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x w : ℂ) (hx : (1/2 : ℝ)≤x.re) :
    AnalyticOnNhd ℂ (fun z =>ramifiedCorrection η u P hs x w z) {z : ℂ | 1/3<z.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_first_analytic_z
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx

theorem ramifiedCorrection_first_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (51/100 : ℝ)≤x.re) (hw : -(1/100 : ℝ)≤w.re) (hz : (17/50 : ℝ)≤z.re) (hxw : 1≤x.re+w.re) :
    ‖ramifiedCorrection η u P hs x w z‖≤193 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  exact ramifiedClosed_first_region_bound p hp hg.1 hg.2 _ _ _ x w z
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) ha
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)) hx hw hz hxw _ (multiplicity_lt_six u p hp)

theorem ramified_product_first_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (η : Character) (u : FreeRow) (x w z : ℂ),
      (51/100 : ℝ)≤x.re → -(1/100 : ℝ)≤w.re → (17/50 : ℝ)≤z.re → 1≤x.re+w.re →
      ‖∏ P∈(ramifiedPrimes S u).attach,
        ramifiedCorrection η u P.val
          (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound 193 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro S hS η u x w z hx hw hz hxw
  rw [norm_prod]
  calc
    _ ≤ ∏ P∈(ramifiedPrimes S u).attach,(193 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P hP
      exact ramifiedCorrection_first_bound η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x w z hx hw hz hxw
    _ = (193 : ℝ)^(ramifiedPrimes S u).card := by simp
    _ ≤ (193 : ℝ)^(IdealMobiusDivisorSum.primeSupport (Ideal.span {u.val})).card := by
      apply pow_le_pow_right₀ (by norm_num)
      rw [←HeckeDeletionBounds.primeSet_card]
      exact Finset.card_filter_le _ _
    _ ≤ _ := hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1)

theorem continuedCorrection_first_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (η : Character) (u : FreeRow) (x w z : ℂ),
      (51/100:ℝ)≤x.re → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      1+eps≤x.re+w.re →
      ‖continuedCorrection S hS η u x w z‖≤C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := ramified_product_first_subpower ε hε
  refine ⟨C*(3/2),by positivity,?_⟩
  intro eps S hS hfirst η u x w z hx hw hz hxw
  have hR := hbound S hS η u x w z hx hw hz (by linarith [hfirst.positive])
  have hU := unramifiedProduct_first_defect eps S hfirst η u x w z hx hz hw hxw
  have hnorm : ‖unramifiedProduct S η u x w z‖≤3/2 := by
    have hh := norm_add_le (unramifiedProduct S η u x w z-1) (1:ℂ)
    simp only [sub_add_cancel,norm_one] at hh
    linarith
  rw [continuedCorrection,norm_mul]
  apply (mul_le_mul hR hnorm (norm_nonneg _) (by positivity)).trans
  exact le_of_eq (by ring)

theorem continuedCorrection_first_analytic_x (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (w z : ℂ)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x=>continuedCorrection S hS η u x w z)
      {x : ℂ | max (51/100:ℝ) (1+eps-w.re)<x.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_first_analytic_x eps S hfirst η u w z hw hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  apply (ramifiedCorrection_first_analytic_x η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    w z (by linarith)).mono
  intro x hx
  change max (51/100:ℝ) (1+eps-w.re)<x.re at hx
  have hh := (lt_of_le_of_lt (le_max_left (51/100:ℝ) (1+eps-w.re)) hx)
  change (1/2:ℝ)<x.re
  linarith

theorem continuedCorrection_first_analytic_w (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w=>continuedCorrection S hS η u x w z)
      {w : ℂ | max (-(1/100:ℝ)) (1+eps-x.re)<w.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_first_analytic_w eps S hfirst η u x z hx hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact (ramifiedCorrection_first_analytic_w η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x z (by linarith) (by linarith)).differentiableOn.analyticOnNhd (Complex.isOpen_re_gt _)

theorem continuedCorrection_first_analytic_z (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    AnalyticOnNhd ℂ (fun z=>continuedCorrection S hS η u x w z) {z : ℂ | (17/50:ℝ)<z.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_first_analytic_z eps S hfirst η u x w hx hw hxw)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  apply (ramifiedCorrection_first_analytic_z η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x w (by linarith)).mono
  intro z hz
  change (17/50:ℝ)<z.re at hz
  change (1/3:ℝ)<z.re
  linarith

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1183

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsFirstNeighborhood.lean; sha256: 4ee3b3925f68a6c07a6642d304f2c7a4513a96a2b438508210c80935a636083f -/
section Source1184
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem unramifiedClosed_first_neighborhood_bound (Q : ℝ) (A eta v x w z : ℂ) (eps : ℝ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (heps : 0<eps) (hx : (101/200:ℝ)≤x.re) (hz : (27/80:ℝ)≤z.re)
    (hw : -(3/200:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedClosed Q A eta v x w z-1‖≤240*Q^(-1-min eps (1/50:ℝ)) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let L := Q^(3/200:ℝ)
  let E := Q^(-(26/25:ℝ))
  let T := Q^(-1-min eps (1/50:ℝ))
  have hL1 : 1≤L := Real.one_le_rpow hQ1 (by norm_num)
  have hT : 0≤T := Real.rpow_nonneg hQ0.le _
  have hV : ‖V‖≤Q^(-(81/40:ℝ)) := by
    rw [show V=coordV Q z from rfl,coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖≤Q^(-(211/200:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖≤L :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖≤Q^(-(101/200:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖≤Q^(-eps) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖≤1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb c : ℝ) (ha : 0≤a) (hb : 0≤b)
      (haa : a≤Q^aa) (hbb : b≤Q^bb) (hc : aa+bb≤c) : a*b≤Q^c := by
    calc
      a*b≤Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _≤Q^c := Real.rpow_le_rpow_of_exponent_le hQ1 hc
  have hRL : ‖R‖*L≤E := hprod _ _ _ _ _ (norm_nonneg _) (by positivity) hR le_rfl (by norm_num)
  have hKV : ‖K‖*‖V‖≤E := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by linarith)
  have hRW : ‖R‖*(1+‖W‖)≤2*E := by
    calc
      _≤‖R‖*(2*L) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _≤2*E := by nlinarith
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hPE : ‖P+D‖≤28*E := by
    have hh := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    dsimp only [P]
    nlinarith
  have hEL : E*L≤T := hprod _ _ _ _ _ (by positivity) (by positivity) le_rfl le_rfl
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hWE : (1+‖W‖)*‖P+D‖≤56*T := by
    calc
      _≤(2*L)*(28*E) := mul_le_mul (by linarith) hPE (norm_nonneg _) (by positivity)
      _≤56*T := by nlinarith
  have hDV : ‖D‖*‖V‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hVW : ‖V‖*‖W‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hDW : ‖D‖*‖W‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (coordD_norm_le Q hQ0 eta v x heta hv) (coordW_norm_le Q hQ0 v w hv)
    (by have := min_le_left eps (1/50:ℝ);linarith)
  have hDVW : ‖D‖*‖V‖*‖W‖≤T := by
    calc
      _ = (‖D‖*‖W‖)*‖V‖ := by ring
      _ ≤ ‖D‖*‖W‖ := mul_le_of_le_one_right (by positivity) (by linarith)
      _ ≤ T := hDW
  have hh := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖≤240*T
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI

end Source1184

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/FirstNeighborhood.lean; sha256: 6f50ca4dbe9ee1aa32d1a25c8cc6da59b7f0ffc97b6313b65176be68f4462d9e -/
section Source1185
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

theorem unramifiedFactor_first_neighborhood_defect (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hP : 4≤P.val.absNorm) (x w z : ℂ) (eps : ℝ) (heps : 0<eps)
    (hx : (101/200:ℝ)≤x.re) (hz : (27/80:ℝ)≤z.re)
    (hw : -(3/200:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedFactor η u P x w z-1‖≤firstPrimeDefectBound eps P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using firstPrimeDefectBound_nonneg eps P
  · apply unramifiedClosed_first_neighborhood_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact heps
    · exact hx
    · exact hz
    · exact hw
    · exact hxw

theorem unramifiedProduct_first_neighborhood_analytic_x (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (w z : ℂ)
    (hw : -(3/200:ℝ)≤w.re) (hz : (27/80:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedProduct S η u x w z)
      {x : ℂ | max (101/200:ℝ) (1+eps-w.re)<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply (unramifiedClosed_first_analytic_x _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro x hx
      change max (101/200:ℝ) (1+eps-w.re)<x.re at hx
      have hx' := (lt_of_le_of_lt (le_max_left (101/200:ℝ) (1+eps-w.re)) hx)
      change (1/2:ℝ)<x.re
      linarith
  · intro P x hx
    have hx' := (lt_of_le_of_lt (le_max_left (101/200:ℝ) (1+eps-w.re)) hx)
    have hxw := (lt_of_le_of_lt (le_max_right (101/200:ℝ) (1+eps-w.re)) hx)
    exact unramifiedFactor_first_neighborhood_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx'.le hz hw (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_neighborhood_analytic_w (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x z : ℂ)
    (hx : (101/200:ℝ)≤x.re) (hz : (27/80:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w=>unramifiedProduct S η u x w z)
      {w : ℂ | max (-(3/200:ℝ)) (1+eps-x.re)<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      exact (unramifiedClosed_first_analytic_w _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith) (by linarith)).mono
          (Set.subset_univ _)
  · intro P w hw
    have hw' := (lt_of_le_of_lt (le_max_left (-(3/200:ℝ)) (1+eps-x.re)) hw)
    have hxw := (lt_of_le_of_lt (le_max_right (-(3/200:ℝ)) (1+eps-x.re)) hw)
    exact unramifiedFactor_first_neighborhood_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw'.le (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_neighborhood_analytic_z (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (101/200:ℝ)≤x.re) (hw : -(3/200:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    AnalyticOnNhd ℂ (fun z=>unramifiedProduct S η u x w z) {z : ℂ | (27/80:ℝ)<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ=>if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [ite_eq_right h]
      apply (unramifiedClosed_first_analytic_z _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro z hz
      change (27/80:ℝ)<z.re at hz
      change (1/3:ℝ)<z.re
      linarith
  · intro P z hz
    exact unramifiedFactor_first_neighborhood_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz.le hw hxw
  · exact hS.half

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1185

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/Series.lean; sha256: d08bcfae4c8d44c9f0902c2867a43fa0da58127559241110e05754211ca8f044 -/
section Source1186
namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def continuedSeries (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (rowCharacter S hS.prime u) w*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x*
      continuedCorrection S hS η u x w z

theorem continuedSeries_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedSeries S hS η u x w z=markedIdealHighSeries S 1 η u.val x w z := by
  have hx0 : x≠0 := by intro h; simp only [h,Complex.zero_re] at hx; linarith
  have hx1 : x≠1 := by intro h; simp only [h,Complex.one_re] at hx; linarith
  rw [continuedSeries,HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,
    high_L_factorization_continued S hS η u x w z hx hw hz,div_eq_mul_inv]

theorem continuedSeries_differentiableAt_x (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)<x.re) (hbeta : HeckeZeroSupremum.beta<x.re)
    (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    DifferentiableAt ℂ (fun x =>continuedSeries S hS η u x w z) x := by
  exact ((HeckeReciprocal.reciprocal_differentiableAt _ hbeta).const_mul _).mul
    ((continuedCorrection_analytic_x S hS η u w z hw hz) x hx).differentiableAt

theorem continuedSeries_differentiableAt_w (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)<w.re) (hz : (4/25 : ℝ)≤z.re)
    (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w =>continuedSeries S hS η u x w z) w := by
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw; linarith
  exact (((LFunction_differentiableAt (rowCharacter S hS.prime u) hw0 hpole).const_mul _).mul_const _).mul
    ((continuedCorrection_analytic_w S hS η u x z hx hz) w hw).differentiableAt

theorem continuedSeries_differentiableAt_z (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)<z.re)
    (hpole : 6*z≠1) :
    DifferentiableAt ℂ (fun z =>continuedSeries S hS η u x w z) z := by
  have hz0 : 6*z≠0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [Complex.mul_re] at he
    linarith
  exact ((((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) hz0 (Or.inl hpole)).comp z
    (differentiableAt_id.const_mul 6)).mul_const _).mul_const _).mul
      ((continuedCorrection_analytic_z S hS η u x w hx hw) z hz).differentiableAt

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1186

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/Origin.lean; sha256: 92338975365e40d1ddec35b9a0c980545f21916886432cb0127ea2ac4feb75e0 -/
section Source1187
namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def continuedHighSeries (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeOrigin.continued (rowCharacter S hS.prime u) w*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x*
    continuedCorrection S hS η u x w z

theorem continuedHighSeries_eq_series (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) (hw0 : w≠0) (hw1 : w≠1) :
    continuedHighSeries S hS η u x w z=continuedSeries S hS η u x w z := by
  rw [continuedHighSeries,HeckeOrigin.continued_eq _ hw0 hw1,continuedSeries]

theorem continuedHighSeries_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedHighSeries S hS η u x w z=markedIdealHighSeries S 1 η u.val x w z := by
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw; linarith
  have hw1 : w≠1 := by intro h; simp only [h,Complex.one_re] at hw; linarith
  rw [continuedHighSeries_eq_series S hS η u x w z hw0 hw1,
    continuedSeries_eq_initial S hS η u x w z hx hw hz]

theorem continuedHighSeries_first_differentiableAt_w (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : max (-(1/100:ℝ)) (1+eps-x.re)<w.re)
    (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=>continuedHighSeries S hS η u x w z) w := by
  exact (((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _).mul
    ((continuedCorrection_first_analytic_w eps S hS hfirst η u x z hx hz) w hw).differentiableAt

theorem continuedHighSeries_first_differentiableAt_x (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hx : max (51/100:ℝ) (1+eps-w.re)<x.re)
    (hbeta : HeckeZeroSupremum.beta<x.re) :
    DifferentiableAt ℂ (fun x=>continuedHighSeries S hS η u x w z) x := by
  exact ((HeckeReciprocal.reciprocal_differentiableAt _ hbeta).const_mul _).mul
    ((continuedCorrection_first_analytic_x eps S hS hfirst η u w z hw hz) x hx).differentiableAt

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1187

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/FirstBoundary.lean; sha256: 33f0229ec0e963c3ed443961e378fd5d943fa5719ecc471d796e1224c2ec32ec -/
section Source1188
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem continuedCorrection_first_boundary_x (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    AnalyticAt ℂ (fun x=>continuedCorrection S hS η u x w z) x := by
  apply AnalyticAt.mul _ ((unramifiedProduct_first_neighborhood_analytic_x (eps/2) S hfirst
    η u w z (by linarith) (by linarith)) x (by change max (101/200:ℝ) (1+eps/2-w.re)<x.re; exact max_lt (by linarith) (by linarith)))
  apply Finset.analyticAt_fun_prod
  intro P hP
  exact (ramifiedCorrection_first_analytic_x η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    w z (by linarith)) x (by change (1/2:ℝ)<x.re; linarith)

theorem continuedCorrection_first_boundary_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    AnalyticAt ℂ (fun w=>continuedCorrection S hS η u x w z) w := by
  apply AnalyticAt.mul _ ((unramifiedProduct_first_neighborhood_analytic_w (eps/2) S hfirst
    η u x z (by linarith) (by linarith)) w (by change max (-(3/200:ℝ)) (1+eps/2-x.re)<w.re; exact max_lt (by linarith) (by linarith)))
  apply Finset.analyticAt_fun_prod
  intro P hP
  exact ((ramifiedCorrection_first_analytic_w η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x z (by linarith) (by linarith)).differentiableOn.analyticOnNhd
      (isOpen_univ : IsOpen (Set.univ : Set ℂ))) w (Set.mem_univ w)

theorem continuedCorrection_first_boundary_z (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    AnalyticAt ℂ (fun z=>continuedCorrection S hS η u x w z) z := by
  apply AnalyticAt.mul _ ((unramifiedProduct_first_neighborhood_analytic_z (eps/2) S hfirst
    η u x w (by linarith) (by linarith) (by linarith)) z (by change (27/80:ℝ)<z.re; linarith))
  apply Finset.analyticAt_fun_prod
  intro P hP
  exact (ramifiedCorrection_first_analytic_z η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x w (by linarith)) z (by change (1/3:ℝ)<z.re; linarith)

theorem continuedHighSeries_first_boundary_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=>continuedHighSeries S hS η u x w z) w := by
  exact (((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _).mul
    (continuedCorrection_first_boundary_w eps heps S hS hfirst η u x w z hx hw hz hxw).differentiableAt

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1188

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/MarkedExclusions.lean; sha256: c5a50d801a7bef905dd7a6d8c76fbdda27db8a4c53f4d7952233fee5ce18775e -/
section Source1189
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical
local notation "O" => HeckeFamily.O

theorem correctionTail_mono {S T : Finset (Ideal O)} (hS : CorrectionTail S) (hst : S⊆T) :
    CorrectionTail T := by
  let inc : {P : PrimeIdeal // P.val∉T}→{P : PrimeIdeal // P.val∉S} :=
    fun P=>⟨P.val,fun h=>P.property (hst h)⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun R : {P : PrimeIdeal // P.val∉S}=>R.val) h)
  constructor
  · intro P hP
    exact hS.norm_four P (fun h=>hP (hst h))
  · apply le_trans _ hS.small
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=>globalPrimeDefectBound_nonneg P.val)
      (fun _=>le_rfl) (globalPrimeDefectBound_summable.subtype _) hS.summable

theorem firstTail_mono {eps : ℝ} {S T : Finset (Ideal O)} (hS : FirstTail eps S) (hst : S⊆T) :
    FirstTail eps T := by
  let inc : {P : PrimeIdeal // P.val∉T}→{P : PrimeIdeal // P.val∉S} :=
    fun P=>⟨P.val,fun h=>P.property (hst h)⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun R : {P : PrimeIdeal // P.val∉S}=>R.val) h)
  refine ⟨hS.positive,?_,?_⟩
  · intro P hP
    exact hS.norm_four P (fun h=>hP (hst h))
  · apply le_trans _ hS.small
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=>firstPrimeDefectBound_nonneg eps P.val)
      (fun _=>le_rfl) ((firstPrimeDefectBound_summable eps hS.positive).subtype _) hS.summable

theorem markedSourceExclusions (S : Finset (Ideal O)) (hS : SourceExclusions S) (T : Finset PrimeIdeal) :
    SourceExclusions (markExclusions S T) := {
  prime := markExclusions_prime S hS.prime T
  bad := hS.bad.trans Finset.subset_union_left
  tail := correctionTail_mono hS.tail Finset.subset_union_left }

theorem marked_firstTail (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S) (T : Finset PrimeIdeal) :
    FirstTail eps (markExclusions S T) := firstTail_mono hS Finset.subset_union_left

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1189

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/MarkedContinuation.lean; sha256: a548f9d9deac0f542435642545b0a3ceb91f90491602c986303ed1a322e193bd -/
section Source1190
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def continuedCompensatedRow (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ) : ℂ :=
  (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeOrigin.continued (rowCharacter S hS.prime u) w*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
  (continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
    ∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z (B P.val) (q P.val))

theorem continuedCompensatedRow_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedCompensatedRow S hS T hT η u x w z B q=spectralCompensatedRow S T η u.val x w z B q := by
  have hx0 : x≠0 := by intro h; simp only [h,Complex.zero_re] at hx;linarith
  have hx1 : x≠1 := by intro h; simp only [h,Complex.one_re] at hx;linarith
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw;linarith
  have hw1 : w≠1 := by intro h; simp only [h,Complex.one_re] at hw;linarith
  unfold continuedCompensatedRow
  rw [HeckeOrigin.continued_eq _ hw0 hw1,HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,
    continuedCorrection_eq_initial (markExclusions S T) (markedSourceExclusions S hS T) η u x w z hx hw hz]
  simp_rw [continuedCompensatedLocal_eq_initial η u _ _ x w z _ _ hx hw hz]
  rw [Finset.prod_attach T (fun P=>compensatedLocalCorrection η u P x w z (B P) (q P)),spectralCompensatedRow_original_L_factorization S hS.prime hS.bad T hT η u x w z B q hx hw hz,
    div_eq_mul_inv]

theorem continuedCompensatedRow_eq_indexed {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let hT : ∀Q∈Finset.univ.image P,Q.val∉S := by
      intro Q hQ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
      exact hPS i
    continuedCompensatedRow S hS (Finset.univ.image P) hT η u x w z
      (fun Q=>star (idealCoeff η Q.val)*(Q.val.absNorm:ℂ)^x)
      (fun Q=>(Q.val.absNorm:ℂ)^(-w))=
      indexedCompensatedHigh η S (fun i=>CompletedGauss.primaryGenerator (P i).val) u.val x w z := by
  dsimp only
  rw [continuedCompensatedRow_eq_initial _ _ _ _ _ _ _ _ _ _ _ hx hw hz,
    indexedCompensatedHigh_eq_spectral η S P hP
      (fun i=>outside_prime_supported S hS.bad (P i) (hPS i)) u.val x w z]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1190

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/SelectedAnalytic.lean; sha256: 7c32cf66016a77406594548d5b96705cbb467eb3227dfa8a579261cda4439854 -/
section Source1191
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem continuedMarkedLocal_eq_quotient (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hV : 1-coordV P.val.absNorm z≠0) :
    continuedMarkedLocal η u P hs x w z=(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z) := by
  rw [ramifiedCorrection_eq_marked]
  field_simp
  ring

theorem selected_V_ne_zero (P : PrimeIdeal) (hQ : (4:ℝ)≤P.val.absNorm) (z : ℂ)
    (hz : (4/25:ℝ)≤z.re) : 1-coordV P.val.absNorm z≠0 := by
  apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
  rw [coordV_norm _ (by linarith : (0:ℝ)<P.val.absNorm)]
  apply rpow_le_half _ _ hQ
  linarith

theorem continuedMarkedLocal_analyticAt_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)<x.re) (hz : (4/25:ℝ)≤z.re) :
    AnalyticAt ℂ (fun x=>continuedMarkedLocal η u P hs x w z) x := by
  have he : (fun x=>continuedMarkedLocal η u P hs x w z)=
      (fun x=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun x=>continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z hz))
  rw [he]
  exact (((ramifiedCorrection_analytic_x η u P hs hQ w z hz) x hx).sub analyticAt_const).div_const

theorem continuedMarkedLocal_differentiable_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (4/25:ℝ)≤z.re) :
    Differentiable ℂ (fun w=>continuedMarkedLocal η u P hs x w z) := by
  have he : (fun w=>continuedMarkedLocal η u P hs x w z)=
      (fun w=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun w=>continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z hz))
  rw [he]
  exact ((ramifiedCorrection_analytic_w η u P hs hQ x z hx hz).sub_const 1).div_const _

theorem continuedMarkedLocal_analyticAt_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (4/25:ℝ)<z.re) :
    AnalyticAt ℂ (fun z=>continuedMarkedLocal η u P hs x w z) z := by
  have hcv := (coordV_differentiable (P.val.absNorm:ℝ) (by linarith)).analyticAt z
  have ha : AnalyticAt ℂ (fun t=>(ramifiedCorrection η u P hs x w t-1)/(1-coordV P.val.absNorm t)) z :=
    (((ramifiedCorrection_analytic_z η u P hs hQ x w hx) z hz).sub analyticAt_const).div
    (analyticAt_const.sub hcv) (selected_V_ne_zero P hQ z hz.le)
  apply ha.congr
  filter_upwards [(Complex.isOpen_re_gt (4/25)).mem_nhds hz] with t ht
  exact (continuedMarkedLocal_eq_quotient η u P hs x w t (selected_V_ne_zero P hQ t ht.le)).symm

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1191

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/SelectedHolomorphic.lean; sha256: cd5fee1af1dbdf98b234cbe3c20af93fe5e7b1a810ec5a82cd1401b269e301c2 -/
section Source1192
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

theorem continuedCompensatedLocal_differentiableAt_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)<x.re) (hz : (4/25:ℝ)≤z.re) :
    DifferentiableAt ℂ (fun x=>continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) x := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := (continuedMarkedLocal_analyticAt_x η u P hs hQ x w z hx hz).differentiableAt
  have hD := coordD_differentiable (P.val.absNorm:ℝ) hQ0 (idealCoeff η P.val) (idealRowHom u.val P.val)
  have hB : Differentiable ℂ (fun x:ℂ=>star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) :=
    (differentiable_id.const_cpow (Or.inl hQc)).const_mul _
  have hd := (open_region_denominators (P.val.absNorm:ℝ) 0 (idealCoeff η P.val)
    (idealRowHom u.val P.val) x z hQ (by simp) (idealCoeff_norm_le_one η _)
    (idealRowHom_norm u.val _) hx.le hz).2.2
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop (disch := first | assumption | exact Or.inl hQc)

theorem continuedCompensatedLocal_differentiable_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (4/25:ℝ)≤z.re) :
    Differentiable ℂ (fun w=>continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := continuedMarkedLocal_differentiable_w η u P hs hQ x z hx hz
  have hW := coordW_differentiable (P.val.absNorm:ℝ) hQ0 (idealRowHom u.val P.val)
  have hq : Differentiable ℂ (fun w:ℂ=>(P.val.absNorm:ℂ)^(-w)) :=
    differentiable_id.neg.const_cpow (Or.inl hQc)
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop

theorem continuedCompensatedLocal_differentiableAt_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (4/25:ℝ)<z.re) :
    DifferentiableAt ℂ (fun z=>continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) z := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hM := (continuedMarkedLocal_analyticAt_z η u P hs hQ x w z hx hz).differentiableAt
  have hV := coordV_differentiable (P.val.absNorm:ℝ) hQ0
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1192

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/MarkedHolomorphic.lean; sha256: dfe0826f8205ad4900214616ea5d6171a69b31534e21c7823a58231aa4458b78 -/
section Source1193
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def physicalCompensatedRow (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) : ℂ :=
  continuedCompensatedRow S hS T hT η u x w z
    (fun P=>star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x)
    (fun P=>(P.val.absNorm:ℂ)^(-w))

theorem physicalCompensatedRow_first_differentiableAt_x (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (7/8:ℝ)<x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) (hbeta : HeckeZeroSupremum.beta<x.re) :
    DifferentiableAt ℂ (fun x=>physicalCompensatedRow S hS T hT η u x w z) x := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (HeckeReciprocal.reciprocal_differentiableAt _ hbeta).const_mul _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_x eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        (by linarith) hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_differentiableAt_x η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z hx (by linarith)

theorem physicalCompensatedRow_first_differentiableAt_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (7/8:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=>physicalCompensatedRow S hS T hT η u x w z) w := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact ((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_w eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        (by linarith) hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact (continuedCompensatedLocal_differentiable_w η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x z hx (by linarith)) w

theorem physicalCompensatedRow_first_differentiableAt_z (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (7/8:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun z=>physicalCompensatedRow S hS T hT η u x w z) z := by
  have hz0 : 6*z≠0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.mul_re] at hh
    linarith
  have hz1 : 6*z≠1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.mul_re] at hh
    linarith
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) hz0 (Or.inl hz1)).comp z
      (differentiableAt_id.const_mul 6)).mul_const _).mul_const _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_z eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        (by linarith) hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_differentiableAt_z η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z hx (by linarith)

theorem unselectedCorrection_subpower (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (T : Finset PrimeIdeal) (η : Character) (u : FreeRow) (x w z : ℂ),
      (7/8:ℝ)≤x.re → (19/20:ℝ)≤w.re → (33/200:ℝ)≤z.re →
      ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ := by
  obtain ⟨C,hC,hbound⟩ := continuedCorrection_subpower δ hδ
  exact ⟨C,hC,fun S hS T η u x w z hx hw hz=>
    hbound (markExclusions S T) (markedSourceExclusions S hS T) η u x w z hx hw hz⟩

theorem unselectedCorrection_first_subpower (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀ (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (T : Finset PrimeIdeal) (η : Character) (u : FreeRow) (x w z : ℂ),
      (51/100:ℝ)≤x.re → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re → 1+eps≤x.re+w.re →
      ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ := by
  obtain ⟨C,hC,hbound⟩ := continuedCorrection_first_subpower δ hδ
  exact ⟨C,hC,fun eps S hS hfirst T η u x w z hx hw hz hxw=>
    hbound eps (markExclusions S T) (markedSourceExclusions S hS T) (marked_firstTail eps S hfirst T)
      η u x w z hx hw hz hxw⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1193

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/TupleFactor.lean; sha256: a49753c5cca61f4bd41ecd88bdd122aa61b5e7beeb89c98e817f7999b85b4fc0 -/
section Source1194
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem physicalCompensatedRow_indexed {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    let hT : ∀Q∈Finset.univ.image P,Q.val∉S := by
      intro Q hQ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
      exact hPS i
    physicalCompensatedRow S hS (Finset.univ.image P) hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,continuedCompensatedLocal η u (P i)
          (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
          (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
          (((P i).val.absNorm:ℂ)^(-w))) := by
  dsimp only
  unfold physicalCompensatedRow continuedCompensatedRow
  congr 2
  symm
  apply Finset.prod_bij (fun i _=>⟨P i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  · intro i _; exact Finset.mem_attach _ _
  · intro i _ j _ h; exact hP (congrArg Subtype.val h)
  · intro Q _
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp Q.property
    exact ⟨i,hi,Subtype.ext he⟩
  · intro i _; rfl

end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source1194

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/WeightedTuple.lean; sha256: 3895f373e22a29a484c883bd5f03c420381fc10de00fc296e9084c02eb178fc5 -/
section Source1195
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem tupleOutside {K : ℕ} (S : Finset (Ideal O)) (P : Fin K→PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) : ∀Q∈Finset.univ.image P,Q.val∉S := by
  intro Q hQ
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
  exact hPS i

def calibratedTupleValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℂ :=
  star ((calibrationForSet S hmax).residueMonoid u.val)*
  (∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1))*
  physicalCompensatedRow S hS (Finset.univ.image P) (tupleOutside S P hPS) η u x w z

theorem calibratedTupleValue_factor {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    calibratedTupleValue S hS hmax η u P hPS W Y x w z=
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
          HeckeOrigin.continued (rowCharacter S hS.prime u) w*
          HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x))*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1)*
          continuedCompensatedLocal η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
            (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
            (((P i).val.absNorm:ℂ)^(-w))) := by
  unfold calibratedTupleValue
  rw [physicalCompensatedRow_indexed S hS P hP hPS]
  simp only [Finset.prod_mul_distrib]
  ring

end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source1195

/- Original source: OAI/NumberTheory/DirichletL/Detector/SelectedPrimeSums.lean; sha256: b9cdb1a0cd961906852b6bf2809c39bcccc566e0db35bdd9bcab4d0cfaae81bf -/
section Source1196
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeSelectedPrimeSums
local notation "O" => ActualEisensteinCubic.O

lemma finite_ideal_count (S : Finset (Ideal O)) (H : ℝ) (hH : 0≤H)
    (hS : ∀I∈S,I≠0) (hN : ∀I∈S,(Ideal.absNorm I:ℝ)≤H) :
    (S.card:ℝ)≤128*H := by
  by_cases hh : 1≤H
  · exact DescentFiberCost.finite_ideal_count_real S H hh hS hN
  · have he : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hI
      have hp : (1:ℝ)≤Ideal.absNorm I := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
      have := hN I hI
      linarith
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

lemma ramified_card_bound (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ, 0<C ∧ ∀ (U : Ideal O), U≠0 → ∀S : Finset (Ideal O),
      ((S.filter (fun P=>P∣U)).card:ℝ)≤C*(Ideal.absNorm U:ℝ)^eps := by
  obtain ⟨C,hC,hb⟩ := IdealDivisorBound.ideal_divisor_small_power eps heps
  refine ⟨C,hC,?_⟩
  intro U hU S
  apply (show ((S.filter (fun P=>P∣U)).card:ℝ)≤(IdealMobiusDivisorSum.idealDivisors U).card from ?_).trans (hb U hU)
  exact_mod_cast Finset.card_le_card (show S.filter (fun P=>P∣U)⊆IdealMobiusDivisorSum.idealDivisors U from by
    intro P hP
    exact (IdealMobiusDivisorSum.mem_idealDivisors hU).mpr (Finset.mem_filter.mp hP).2)

def annularPower (a b r : ℝ) : ℝ := max (a^r) (b^r)

lemma annularPower_nonneg (a b r : ℝ) (ha : 0<a) : 0≤annularPower a b r :=
  (Real.rpow_nonneg ha.le _).trans (le_max_left _ _)

lemma annular_rpow (a b P q r : ℝ) (ha : 0<a) (hb : 0<b) (hP : 0<P)
    (hqa : a*P≤q) (hqb : q≤b*P) : q^r≤annularPower a b r*P^r := by
  have hq : 0<q := (mul_pos ha hP).trans_le hqa
  by_cases hr : 0≤r
  · calc
      q^r≤(b*P)^r := Real.rpow_le_rpow hq.le hqb hr
      _=b^r*P^r := Real.mul_rpow hb.le hP.le
      _≤annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hP.le _)
  · calc
      q^r≤(a*P)^r := Real.rpow_le_rpow_of_nonpos (mul_pos ha hP) hqa (by linarith)
      _=a^r*P^r := Real.mul_rpow ha.le hP.le
      _≤annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hP.le _)

theorem annular_slot_majorant (eps a b r d : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) :
    ∃C : ℝ, 0<C ∧ ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀S : Finset (Ideal O), (∀I∈S,I≠0) →
      (∀I∈S,a*P≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤b*P) →
      (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1))
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨D,hD,hdiv⟩ := ramified_card_bound eps heps
  let A := annularPower a b (r-1)
  let B := annularPower a b (r-1+d)
  have hA : 0≤A := annularPower_nonneg a b _ ha
  have hB : 0≤B := annularPower_nonneg a b _ ha
  refine ⟨1+128*b*A+D*B,by positivity,?_⟩
  intro U hU P hP S hS hSP
  have hP0 : 0<P := by linarith
  have hU1 : (1:ℝ)≤Ideal.absNorm U := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU)
  have hUpow : 1≤(Ideal.absNorm U:ℝ)^eps := Real.one_le_rpow hU1 heps.le
  have hq (I : Ideal O) (hI : I∈S) : 0<(Ideal.absNorm I:ℝ) :=
    (mul_pos ha hP0).trans_le (hSP I hI).1
  have hc := finite_ideal_count S (b*P) (by positivity) hS (fun I hI=>(hSP I hI).2)
  have heP : P*P^(r-1)=P^r := by
    calc
      _=P^(1:ℝ)*P^(r-1) := by rw [Real.rpow_one]
      _=P^r := by rw [←Real.rpow_add hP0];congr 1;ring
  have hfirst : (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1))≤128*b*A*P^r := by
    calc
      _≤∑_I∈S,A*P^(r-1) := Finset.sum_le_sum (fun I hI=>annular_rpow a b P _ _ ha hb hP0 (hSP I hI).1 (hSP I hI).2)
      _=(S.card:ℝ)*(A*P^(r-1)) := by simp
      _≤(128*(b*P))*(A*P^(r-1)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=128*b*A*(P*P^(r-1)) := by ring
      _=128*b*A*P^r := by rw [heP]
  have hsecond : (∑I∈S.filter (fun I=>I∣U),(Ideal.absNorm I:ℝ)^(r-1+d))≤
      D*B*(Ideal.absNorm U:ℝ)^eps*P^r := by
    have hpP : P^(r-1+d)≤P^r := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
    calc
      _≤∑_I∈S.filter (fun I=>I∣U),B*P^(r-1+d) := by
        apply Finset.sum_le_sum
        intro I hI
        exact annular_rpow a b P _ _ ha hb hP0 (hSP I (Finset.mem_filter.mp hI).1).1 (hSP I (Finset.mem_filter.mp hI).1).2
      _=((S.filter (fun I=>I∣U)).card:ℝ)*(B*P^(r-1+d)) := by simp
      _≤(D*(Ideal.absNorm U:ℝ)^eps)*(B*P^r) := by
        gcongr
        exact hdiv U hU S
      _=D*B*(Ideal.absNorm U:ℝ)^eps*P^r := by ring
  have hsum : (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1))≤
      (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1))+
        ∑I∈S.filter (fun I=>I∣U),(Ideal.absNorm I:ℝ)^(r-1+d) := by
    rw [Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro I hI
    split_ifs
    · rw [←Real.rpow_add (hq I hI)]
      exact le_add_of_nonneg_left (by positivity)
    · simp only [mul_one,add_zero,le_refl]
  apply hsum.trans
  have hup : 128*b*A*P^r≤128*b*A*(Ideal.absNorm U:ℝ)^eps*P^r := by
    nlinarith [mul_nonneg (show 0≤128*b*A*P^r by positivity) (show 0≤(Ideal.absNorm U:ℝ)^eps-1 by linarith)]
  nlinarith [mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤Ideal.absNorm U) eps) (Real.rpow_nonneg hP0.le r)]

theorem weighted_slot_bound (eps a b r d B K : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) (hB : 0≤B) (hK : 0≤K) :
    ∃C : ℝ, 0<C ∧ ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀(S : Finset (Ideal O)), (∀I∈S,I≠0) → ∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc a b → (∀y,‖W y‖≤B) →
    ∀(G : Ideal O→ℂ), (∀I∈S,‖G I‖≤K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) →
    ∀z : ℂ, z.re=r →
      (∑I∈S,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖)
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨C,hC,hmajor⟩ := annular_slot_majorant eps a b r d heps ha hb hd
  refine ⟨(B*K+1)*C,by positivity,?_⟩
  intro U hU P hP S hS W hWS hWB G hG z hz
  have hP0 : 0<P := by linarith
  let T := S.filter (fun I=>W ((Ideal.absNorm I:ℝ)/P)≠0)
  have hTS : T⊆S := Finset.filter_subset _ _
  have hbounds (I : Ideal O) (hI : I∈T) : a*P≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤b*P := by
    have ht := hWS (show (Ideal.absNorm I:ℝ)/P∈Function.support W from (Finset.mem_filter.mp hI).2)
    exact ⟨(le_div_iff₀ hP0).mp ht.1,(div_le_iff₀ hP0).mp ht.2⟩
  have he : (∑I∈S,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖)=
      ∑I∈T,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖ := by
    symm
    apply Finset.sum_subset hTS
    intro I hI hn
    have hw : W ((Ideal.absNorm I:ℝ)/P)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
    simp only [hw,zero_mul,norm_zero]
  rw [he]
  have hpoint (I : Ideal O) (hI : I∈T) :
      ‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖≤
        (B*K)*((Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) := by
    have hN : (0:ℝ)<Ideal.absNorm I := (mul_pos ha hP0).trans_le (hbounds I hI).1
    have hc : ‖(Ideal.absNorm I:ℂ)^(z-1)‖=(Ideal.absNorm I:ℝ)^(r-1) := by
      simpa only [Complex.ofReal_natCast,Complex.sub_re,Complex.one_re,hz] using
        Complex.norm_cpow_eq_rpow_re_of_pos hN (z-1)
    simp only [norm_mul,hc]
    calc
      _≤B*(Ideal.absNorm I:ℝ)^(r-1)*(K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) := by
        gcongr
        · exact hWB _
        · exact hG I (hTS hI)
      _=_ := by ring
  have hmain := hmajor U hU P hP T (fun I hI=>hS I (hTS hI)) hbounds
  calc
    _≤∑I∈T,(B*K)*((Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) :=
      Finset.sum_le_sum hpoint
    _=(B*K)*∑I∈T,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1) :=
      (Finset.mul_sum _ _ _).symm
    _≤(B*K)*(C*(Ideal.absNorm U:ℝ)^eps*P^r) := mul_le_mul_of_nonneg_left hmain (mul_nonneg hB hK)
    _≤((B*K+1)*C)*(Ideal.absNorm U:ℝ)^eps*P^r := by
      nlinarith [mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by positivity : (0:ℝ)≤Ideal.absNorm U) eps))
        (Real.rpow_nonneg hP0.le r)]

end SevenEighths.ProbeSelectedPrimeSums
end

end OAI

end Source1196

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/SelectedBounds.lean; sha256: e444da75b1ec0f7d91f5eb9ac4b8949221545c9fd09722de8ea5c72a4c6a233e -/
section Source1197
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma continuedCompensatedLocal_ramified_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤P.val.absNorm)
    (x w z : ℂ) (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤
        385*(P.val.absNorm:ℝ)^(max (1-w.re) 0) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  rw [continuedCompensatedLocal_ramified η u P hs hP x w z]
  have hb := ramifiedSelected_bound p hp hg.1 hg.2 _ _ _ x w z
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) ha
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)) hx hw hz
    (multiplicity p u.val) (multiplicity_lt_six u p hp)
  simpa only [hspan] using hb

lemma continuedCompensatedLocal_unramified_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : ¬P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤P.val.absNorm)
    (x w z : ℂ) (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤961 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hnot : ¬p∣u.val := by
    intro hd
    apply hP
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hu : IsCoprime u.val p := (hp.irreducible.coprime_iff_not_dvd.mpr hnot).symm
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hV : ‖coordV P.val.absNorm z‖<1 := by
    exact (first_region_V_half _ hQ z hz).trans_lt (by norm_num)
  have hR : ‖coordR P.val.absNorm (actualAPhase η p) x z‖<1 := by
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact (rpow_le_half _ _ hQ (by linarith)).trans_lt (by norm_num)
  rw [continuedCompensatedLocal_unramified η u P hs hP x w z hV hR]
  have hb := actualUnramifiedSelected_bound η p u.val hg.1 hg.2 hu (hspan.symm ▸ hQ) x w z hx hw hz
  have he : idealCoeff η P.val=elementCoeff η p := by rw [←hspan,idealCoeff_span η hp.ne_zero]
  have hv : idealRowHom u.val P.val=actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    rw [←hspan,idealRowHom_prime u.val (Ideal.span {p}) hg.1]
  simpa only [actualUnramifiedSelected,hspan,he,hv] using hb

lemma continuedCompensatedLocal_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm)
    (x w z : ℂ) (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤
        961*(if P.val∣Ideal.span {u.val} then (P.val.absNorm:ℝ)^(max (1-w.re) 0) else 1) := by
  by_cases hp : P.val∣Ideal.span {u.val}
  · rw [ite_eq_left hp]
    apply (continuedCompensatedLocal_ramified_bound η u P hs hp hQ x w z hx hw hz).trans
    gcongr
    norm_num
  · simpa only [ite_eq_right hp,mul_one] using continuedCompensatedLocal_unramified_bound η u P hs hp hQ x w z hx hw hz

end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source1197

/- Original source: OAI/NumberTheory/DirichletL/Detector/SelectedPrimeIndexed.lean; sha256: 9f5cea7597fcf4769345e3c27da5f39b34b0fc2ad9cb109674a0b28aab6f5295 -/
section Source1198
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeSelectedPrimeSums
local notation "O" => ActualEisensteinCubic.O

lemma weighted_slot_bound_indexed (eps a b r d B K : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) (hB : 0≤B) (hK : 0≤K) :
    ∃C : ℝ, 0<C ∧ ∀{ι : Type*} (f : ι→Ideal O), Function.Injective f →
    ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀(S : Finset ι), (∀i∈S,f i≠0) → ∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc a b → (∀y,‖W y‖≤B) →
    ∀(G : ι→ℂ), (∀i∈S,‖G i‖≤K*(if f i∣U then (Ideal.absNorm (f i):ℝ)^d else 1)) →
    ∀z : ℂ, z.re=r →
      (∑i∈S,‖W ((Ideal.absNorm (f i):ℝ)/P)*(Ideal.absNorm (f i):ℂ)^(z-1)*G i‖)
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨C,hC,hmain⟩ := weighted_slot_bound eps a b r d B K heps ha hb hd hB hK
  refine ⟨C,hC,?_⟩
  intro ι f hf U hU P hP S hS W hWS hWB G hG z hz
  let G' : Ideal O→ℂ := Function.extend f G (fun _=>0)
  have he (i : ι) : G' (f i)=G i := hf.extend_apply G (fun _=>0) i
  have hI (I : Ideal O) (hI : I∈S.image f) : I≠0 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact hS i hi
  have hg (I : Ideal O) (hI : I∈S.image f) :
      ‖G' I‖≤K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    rw [he]
    exact hG i hi
  have hh := hmain U hU P hP (S.image f) hI W hWS hWB G' hg z hz
  rw [Finset.sum_image hf.injOn] at hh
  simpa only [he] using hh

end SevenEighths.ProbeSelectedPrimeSums
end

end OAI

end Source1198

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/SlotSums.lean; sha256: eb5af8ffcf2ceb8cdecf67b8a272979e41fcd05168cc8445e3a90d031c865975 -/
section Source1199
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem continued_selected_slot_bound (eps a b r B : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (T : Finset PrimeIdeal)
      (hT : ∀P∈T,Supported P.val ∧ (4:ℝ)≤P.val.absNorm)
      (Y : ℝ),1≤Y → ∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b →
      (∀y,‖W y‖≤B) → ∀(x w z : ℂ),(7/8:ℝ)≤x.re → (1/2:ℝ)≤w.re → z.re=r →
      (∑P : T,‖W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*
        continuedCompensatedLocal η u P.val (hT P.val P.property).1 x w z
          (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))‖)
      ≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*Y^r := by
  obtain ⟨C,hC,hmain⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed eps a b r (1/2) B 961
    heps ha hb (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro η u T hT Y hY W hWS hWB x w z hx hw hz
  let f : T→Ideal O := fun P=>P.val.val
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    exact Subtype.ext h
  let G : T→ℂ := fun P=>continuedCompensatedLocal η u P.val (hT P.val P.property).1 x w z
    (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))
  have hg (P : T) (_ : P∈Finset.univ) : ‖G P‖≤
      961*(if f P∣Ideal.span {u.val} then (Ideal.absNorm (f P):ℝ)^(1/2:ℝ) else 1) := by
    have hh := continuedCompensatedLocal_bound η u P.val (hT P.val P.property).1
      (hT P.val P.property).2 x w z hx hw (by rw [hz];exact hr)
    apply hh.trans
    by_cases hp : f P∣Ideal.span {u.val}
    · simp only [show P.val.val=f P from rfl,ite_eq_left hp]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by have := (hT P.val P.property).2;change 1≤(P.val.val.absNorm:ℝ);linarith)
        (max_le (by linarith) (by norm_num))
    · simp only [show P.val.val=f P from rfl,ite_eq_right hp,le_refl]
  exact hmain f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _=>P.val.property.ne_zero) W hWS hWB G hg z hz

end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source1199
