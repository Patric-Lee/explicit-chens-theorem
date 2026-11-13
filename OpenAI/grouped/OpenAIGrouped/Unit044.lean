import OpenAIGrouped.Unit007
import OpenAIGrouped.Unit043
import OpenAIGrouped.Unit034
import OpenAIGrouped.Unit039
import OpenAIGrouped.Unit033
import OpenAIGrouped.Unit042
import OpenAIGrouped.Unit032
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OpenAIGrouped.Unit030

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramIdealSummation.lean; sha256: 4959986e463934cb7fb75ad973ffff351661e0d51592a6c1bfe460fc842bdf6d -/
section Source1760
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

def gramIdealNorm (I : SupportedIdeal) : ℝ := Ideal.absNorm I.val

lemma gramIdealNorm_pos (I : SupportedIdeal) : 0 < gramIdealNorm I := by
  unfold gramIdealNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property.1)

lemma gramIdealNorm_one_le (I : SupportedIdeal) : 1 ≤ gramIdealNorm I := by
  unfold gramIdealNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property.1)

theorem supportedIdeal_rpow_summable (r : ℝ) (hr : r < -1) :
    Summable (fun I : SupportedIdeal => gramIdealNorm I ^ r) := by
  have hs := CubicEisenstein.fullIdealWeight_summable_norm ((-r:ℝ):ℂ)
    (by simp only [Complex.ofReal_re]; linarith)
  have hinj : Function.Injective (fun I : SupportedIdeal => I.val) := Subtype.val_injective
  have ht := hs.comp_injective hinj
  apply ht.congr
  intro I
  rw [Function.comp_apply,CubicEisenstein.fullIdealWeight,ite_eq_right I.property.1]
  have he : (Ideal.absNorm I.val:ℂ) = ((gramIdealNorm I:ℝ):ℂ) := by simp [gramIdealNorm]
  rw [he,Complex.norm_cpow_eq_rpow_re_of_pos (gramIdealNorm_pos I)]
  simp only [Complex.neg_re,Complex.ofReal_re,neg_neg]

theorem supportedIdeal_rpow_finite_bound (r : ℝ) (hr : r < -1) :
    ∃ K : ℝ, 0 < K ∧ ∀ F : Finset SupportedIdeal,
      (∑ I ∈ F, gramIdealNorm I ^ r) ≤ K := by
  have hs := supportedIdeal_rpow_summable r hr
  let K := 1 + ∑' I : SupportedIdeal, gramIdealNorm I ^ r
  have hn : 0 ≤ ∑' I : SupportedIdeal, gramIdealNorm I ^ r :=
    tsum_nonneg (fun I => Real.rpow_nonneg (gramIdealNorm_pos I).le _)
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro F
  exact (hs.sum_le_tsum F (fun I _ => Real.rpow_nonneg (gramIdealNorm_pos I).le _)).trans
    (by dsimp [K]; linarith)

lemma ideal_sum_min_power_bound (t : ℝ) (ht : 0 < t) (A : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hA : θ ≤ A) : min 1 (t^A) ≤ t^θ := by
  by_cases h : t ≤ 1
  · apply (min_le_right _ _).trans
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge ht h hA
  · exact (min_le_left _ _).trans (Real.one_le_rpow (le_of_not_ge h) hθ)

lemma gram_ideal_term_bound (δ Λ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hΛ : 0 < Λ) (A : ℕ) (hA : 1 ≤ A) (I J : SupportedIdeal) :
    gramIdealNorm I ^ (-2:ℝ) * gramIdealNorm J ^ (-2:ℝ) *
      min 1 ((gramIdealNorm I*gramIdealNorm J/Λ)^A) ≤
      Λ^(-1+δ) * (gramIdealNorm I^(-1-δ) * gramIdealNorm J^(-1-δ)) := by
  have hi := gramIdealNorm_pos I
  have hj := gramIdealNorm_pos J
  have ha : (1-δ:ℝ) ≤ A := by
    have hh : (1:ℝ) ≤ A := by exact_mod_cast hA
    linarith
  have hm := ideal_sum_min_power_bound (gramIdealNorm I*gramIdealNorm J/Λ)
    (by positivity) A (1-δ) (by linarith) ha
  apply (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq
  rw [Real.div_rpow (by positivity) hΛ.le,Real.mul_rpow hi.le hj.le,
    div_eq_mul_inv,← Real.rpow_neg hΛ.le]
  have hi' : gramIdealNorm I^(-2:ℝ)*gramIdealNorm I^(1-δ)=gramIdealNorm I^(-1-δ) := by
    rw [←Real.rpow_add hi]
    congr 1
    ring
  have hj' : gramIdealNorm J^(-2:ℝ)*gramIdealNorm J^(1-δ)=gramIdealNorm J^(-1-δ) := by
    rw [←Real.rpow_add hj]
    congr 1
    ring
  rw [show -(1-δ) = -1+δ by ring]
  calc
    _ = Λ^(-1+δ)*((gramIdealNorm I^(-2:ℝ)*gramIdealNorm I^(1-δ))*
        (gramIdealNorm J^(-2:ℝ)*gramIdealNorm J^(1-δ))) := by ring
    _ = _ := by rw [hi',hj']

theorem gram_supported_double_sum (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : ℕ), 1 ≤ A → ∀ (Λ : ℝ), 0 < Λ →
      ∀ (F G : Finset SupportedIdeal),
      (∑ I ∈ F, ∑ J ∈ G, gramIdealNorm I^(-2:ℝ) * gramIdealNorm J^(-2:ℝ) *
        min 1 ((gramIdealNorm I*gramIdealNorm J/Λ)^A)) ≤ K*Λ^(-1+δ) := by
  obtain ⟨C,hC,hb⟩ := supportedIdeal_rpow_finite_bound (-1-δ) (by linarith)
  refine ⟨C^2, by positivity, ?_⟩
  intro A hA Λ hΛ F G
  have hF := hb F
  have hG := hb G
  have hGn : 0 ≤ ∑ J ∈ G, gramIdealNorm J^(-1-δ) :=
    Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (gramIdealNorm_pos J).le _)
  calc
    _ ≤ ∑ I ∈ F, ∑ J ∈ G, Λ^(-1+δ)*
        (gramIdealNorm I^(-1-δ)*gramIdealNorm J^(-1-δ)) :=
      Finset.sum_le_sum (fun I _ => Finset.sum_le_sum
        (fun J _ => gram_ideal_term_bound δ Λ hδ hδ1 hΛ A hA I J))
    _ = Λ^(-1+δ)*((∑ I ∈ F, gramIdealNorm I^(-1-δ))*
        (∑ J ∈ G, gramIdealNorm J^(-1-δ))) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ Λ^(-1+δ)*C^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [pow_two] using mul_le_mul hF hG hGn hC.le
    _ = _ := by ring

theorem gram_supported_exceptional_sum (ε : ℝ) (_hε : 0 ≤ ε) (hε1 : ε < 1/6) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F G : Finset SupportedIdeal),
      (∑ I ∈ F, ∑ J ∈ G,
        gramIdealNorm I^(-7/6+ε:ℝ)*gramIdealNorm J^(-2:ℝ)) ≤ K := by
  obtain ⟨C,hC,hb⟩ := supportedIdeal_rpow_finite_bound (-7/6+ε) (by linarith)
  obtain ⟨D,hD,hd⟩ := supportedIdeal_rpow_finite_bound (-2) (by norm_num)
  refine ⟨C*D, by positivity, ?_⟩
  intro F G
  rw [← Finset.sum_mul_sum]
  exact mul_le_mul (hb F) (hd G)
    (Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (gramIdealNorm_pos J).le _)) hC.le

end SevenEighths.ProbeGramCommon

end

end OAI

end Source1760

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramPrefactor.lean; sha256: 00f30d368754a0c3c4db1f2da0de68d552066455dc002bbe2045d4e2d463c492 -/
section Source1761
namespace OAI

noncomputable section
namespace SevenEighths.ProbeGramCommon

lemma nonexceptional_prefactor (c d F P Y Q : ℝ)
    (hc : 0<c) (hd : 0<d) (hF : 0<F) (hP : 0<P) (hY : 0<Y) (A : ℕ) :
    (Q/Y^3)*c*(Y/(c*d))^2*(P/c)*min 1 ((F*c*(P/c)/(Y/(c*d)))^A)=
      (Q/Y)*P*(c^(-2:ℝ)*d^(-2:ℝ)*min 1 ((c*d/(Y/(F*P)))^A)) := by
  have he : F*c*(P/c)/(Y/(c*d))=c*d/(Y/(F*P)) := by field_simp
  rw [he,Real.rpow_neg hc.le,Real.rpow_neg hd.le,Real.rpow_two,Real.rpow_two]
  field_simp

lemma exceptional_prefactor (c d F P Y Q ε : ℝ)
    (hc : 0<c) (hd : 0<d) (hF : 0<F) (hP : 0<P) (hY : 0<Y) :
    (Q/Y^3)*c*(Y/(c*d))^2*(F*c)^ε*(P/c)^(1/6:ℝ)=
      (Q/Y)*F^ε*P^(1/6:ℝ)*(c^(-7/6+ε:ℝ)*d^(-2:ℝ)) := by
  rw [Real.mul_rpow hF.le hc.le,Real.div_rpow hP.le hc.le,
    show (-7/6+ε:ℝ)=ε+(-1)+(-(1/6)) by ring,
    Real.rpow_add hc,Real.rpow_add hc,Real.rpow_neg_one,
    Real.rpow_neg hc.le,Real.rpow_neg hd.le,Real.rpow_two]
  field_simp

lemma supported_nonexceptional_prefactor (C D : SupportedIdeal) (F P Y Q : ℝ)
    (hF : 0<F) (hP : 0<P) (hY : 0<Y) (A : ℕ) :
    (Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
      min 1 ((F*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A)=
      (Q/Y)*P*(gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(F*P)))^A)) :=
  nonexceptional_prefactor _ _ _ _ _ _ (gramIdealNorm_pos C) (gramIdealNorm_pos D) hF hP hY A

lemma supported_exceptional_prefactor (C D : SupportedIdeal) (F P Y Q ε : ℝ)
    (hF : 0<F) (hP : 0<P) (hY : 0<Y) :
    (Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*
      (F*gramIdealNorm C)^ε*(P/gramIdealNorm C)^(1/6:ℝ)=
      (Q/Y)*F^ε*P^(1/6:ℝ)*(gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) :=
  exceptional_prefactor _ _ _ _ _ _ _ (gramIdealNorm_pos C) (gramIdealNorm_pos D) hF hP hY

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1761

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramIdealMass.lean; sha256: a9124c17ba994abe66240bba7eef0eaf47fdb4fd58274f181d60ab366be5c72e -/
section Source1762
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma normalized_double_sum_bound (F G : Finset SupportedIdeal) (α V : SupportedIdeal→SupportedIdeal→ℂ)
    (hα : ∀C∈F,∀D∈G,‖α C D‖≤1) (p : ℝ) (hp : 0≤p) :
    ‖(p:ℂ)*(∑C∈F,∑D∈G,α C D*V C D)‖≤∑C∈F,∑D∈G,p*‖V C D‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  calc
    _≤p*(∑C∈F,∑D∈G,‖α C D*V C D‖) := mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _=>norm_sum_le _ _))) hp
    _≤p*(∑C∈F,∑D∈G,‖V C D‖) := by
      apply mul_le_mul_of_nonneg_left _ hp
      apply Finset.sum_le_sum
      intro C hC
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hα C hC D hD) (norm_nonneg _)).trans_eq (one_mul _)
    _=_ := by simp only [Finset.mul_sum]

theorem canonical_nonexceptional_ideal_sum (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (A : ℕ) (hA : 2<A) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a b)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (F G : Finset SupportedIdeal)(E : SupportedIdeal→SupportedIdeal→Finset GramFrequency)
      (α : SupportedIdeal→SupportedIdeal→ℂ),
      (∀C∈F,∀D∈G,‖α C D‖≤1)→(∀C∈F,∀D∈G,∀k∈E C D,¬ExceptionalFrequency S hS C k)→
      ∀(U : SchwartzMap ℝ ℂ)(v P Y Q : ℝ),0<P→0<Y→0≤Q→
        ‖((Q/Y^3:ℝ):ℂ)*(∑C∈F,∑D∈G,α C D*∑k∈E C D,
          canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
            ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C))
            (Y/(gramIdealNorm C*gramIdealNorm D)))‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P*
          (Y/((Ideal.absNorm (jointFixedModulus S hS):ℝ)*P))^(-1+δ) := by
  obtain ⟨J,H₀,hfreq⟩ := canonical_nonexceptional_frequency_sum A hA a b ha hab
  obtain ⟨L,hL,hideal⟩ := gram_supported_double_sum δ hδ hδ1
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hfreq⟩ := hfreq W hs hW
  refine ⟨K*L,mul_pos hK hL,?_⟩
  intro S hS σ F G E α hα hE U v P Y Q hP hY hQ
  let M : ℝ := Ideal.absNorm (jointFixedModulus S hS)
  have hM : 0<M := by dsimp [M];exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (jointFixedModulus_nonzero S hS))
  let V := fun C D : SupportedIdeal=>∑k∈E C D,
    canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
      ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C)) (Y/(gramIdealNorm C*gramIdealNorm D))
  let B := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P
  have hB : 0≤B := by dsimp [B];positivity
  have ht (C D : SupportedIdeal) (hC : C∈F) (hD : D∈G) :
      (Q/Y^3)*‖V C D‖≤B*(gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := by
    have hc := gramIdealNorm_pos C
    have hd := gramIdealNorm_pos D
    have hh := hfreq S hS σ C (E C D) (hE C hC D hD) (primaryGenerator D.val) U v
      (P/gramIdealNorm C) (Y/(gramIdealNorm C*gramIdealNorm D)) (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0≤Q/Y^3 by positivity)
    apply hh'.trans_eq
    change (Q/Y^3)*(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
      gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
      min 1 ((M*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A))=_
    calc
      _=(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J)*
        ((Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
        min 1 ((M*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A)) := by ring
      _=_ := by rw [supported_nonexceptional_prefactor C D M P Y Q hM hP hY A];dsimp [B];ring
  calc
    _≤∑C∈F,∑D∈G,(Q/Y^3)*‖V C D‖ := normalized_double_sum_bound F G α V hα _ (by positivity)
    _≤∑C∈F,∑D∈G,B*(gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun D hD=>ht C D hC hD))
    _=B*(∑C∈F,∑D∈G,gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := by simp only [Finset.mul_sum]
    _≤B*(L*(Y/(M*P))^(-1+δ)) := mul_le_mul_of_nonneg_left (hideal A (by omega) _ (by positivity) F G) hB
    _=_ := by dsimp [B,M];ring

theorem canonical_exceptional_ideal_sum (ε : ℝ) (hε : 0<ε) (hε1 : ε<1/6)
    (a b M₀ : ℝ) (ha : 0<a) (hb : 0≤b) (hM₀ : 0≤M₀) :
    ∃H₀ : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀(W : ℝ→ℂ)(_hcompact : HasCompactSupport W),
      (Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤M₀)→
      ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (F G : Finset SupportedIdeal)(E : SupportedIdeal→SupportedIdeal→Finset GramFrequency)
      (α : SupportedIdeal→SupportedIdeal→ℂ),
      (∀C∈F,∀D∈G,‖α C D‖≤1)→(∀C∈F,∀D∈G,∀k∈E C D,ExceptionalFrequency S hS C k)→
      ∀(U : SchwartzMap ℝ ℂ)(v P Y Q : ℝ),0<P→0<Y→0≤Q→
        ‖((Q/Y^3:ℝ):ℂ)*(∑C∈F,∑D∈G,α C D*∑k∈E C D,
          canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
            ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C))
            (Y/(gramIdealNorm C*gramIdealNorm D)))‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*
          (Ideal.absNorm (jointFixedModulus S hS):ℝ)^ε*P^(1/6:ℝ) := by
  obtain ⟨H₀,K,hK,hfreq⟩ := canonical_exceptional_frequency_sum a b M₀ ε ha hb hM₀ hε
  obtain ⟨L,hL,hideal⟩ := gram_supported_exceptional_sum ε hε.le hε1
  refine ⟨H₀,K*L,mul_pos hK hL,?_⟩
  intro W hcompact hs hW S hS σ F G E α hα hE U v P Y Q hP hY hQ
  let M : ℝ := Ideal.absNorm (jointFixedModulus S hS)
  have hM : 0<M := by dsimp [M];exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (jointFixedModulus_nonzero S hS))
  let V := fun C D : SupportedIdeal=>∑k∈E C D,
    canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
      ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C)) (Y/(gramIdealNorm C*gramIdealNorm D))
  let B := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*M^ε*P^(1/6:ℝ)
  have hB : 0≤B := by dsimp [B];positivity
  have ht (C D : SupportedIdeal) (hC : C∈F) (hD : D∈G) :
      (Q/Y^3)*‖V C D‖≤B*(gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) := by
    have hc := gramIdealNorm_pos C
    have hd := gramIdealNorm_pos D
    have hh := hfreq W hcompact hs hW U S hS σ C (E C D) (hE C hC D hD) (primaryGenerator D.val) v
      (P/gramIdealNorm C) (Y/(gramIdealNorm C*gramIdealNorm D)) (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0≤Q/Y^3 by positivity)
    apply hh'.trans_eq
    change (Q/Y^3)*(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*
      gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(M*gramIdealNorm C)^ε*(P/gramIdealNorm C)^(1/6:ℝ))=_
    calc
      _=(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        ((Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(M*gramIdealNorm C)^ε*(P/gramIdealNorm C)^(1/6:ℝ)) := by ring
      _=_ := by rw [supported_exceptional_prefactor C D M P Y Q ε hM hP hY];dsimp [B];ring
  calc
    _≤∑C∈F,∑D∈G,(Q/Y^3)*‖V C D‖ := normalized_double_sum_bound F G α V hα _ (by positivity)
    _≤∑C∈F,∑D∈G,B*(gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) :=
      Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun D hD=>ht C D hC hD))
    _=B*(∑C∈F,∑D∈G,gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) := by simp only [Finset.mul_sum]
    _≤B*L := mul_le_mul_of_nonneg_left (hideal F G) hB
    _=_ := by dsimp [B,M];ring

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1762

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramSourceDivisors.lean; sha256: fddf89c1f2343ff523d821f0e887934e26e911abfa45f3d18b5616424135faf0 -/
section Source1763
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
open CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def sourceDivisors (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C : SupportedIdeal) : Finset SupportedIdeal :=
  (divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val).preimage
    Subtype.val Subtype.val_injective.injOn
lemma sourceDivisors_mem (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C D : SupportedIdeal) :
    D∈sourceDivisors W hW Y hY C ↔
      D.val∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val := Finset.mem_preimage

def sourceDivisorUnion (F : Finset SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) : Finset SupportedIdeal :=
  F.biUnion (sourceDivisors W hW Y hY)

def sourceMobiusWeight (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C D : SupportedIdeal) : ℂ :=
  if D∈sourceDivisors W hW Y hY C then (moebius D.val:ℂ) else 0
lemma sourceMobiusWeight_norm (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C D : SupportedIdeal) :
    ‖sourceMobiusWeight W hW Y hY C D‖≤1 := by
  unfold sourceMobiusWeight
  split_ifs
  · exact CubicEisenstein.norm_ideal_moebius_le_one _
  · simp

lemma sourceDivisors_sum (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y)
    (C : SupportedIdeal) (f : Id→ℂ) :
    (∑D∈sourceDivisors W hW Y hY C,f D.val)=
      ∑D∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val,f D := by
  apply Finset.sum_bij (fun D _=>D.val)
  · intro D hD;exact (sourceDivisors_mem W hW Y hY C D).mp hD
  · intro D hD E hE h;exact Subtype.val_injective h
  · intro D hD
    refine ⟨⟨D,divisorPool_supported _ _ hD⟩,?_,rfl⟩
    exact (sourceDivisors_mem W hW Y hY C _).mpr hD
  · intro D hD;rfl

lemma sourceMobiusWeight_rectangle (F : Finset SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y : ℝ) (hY : 0<Y) (C : SupportedIdeal) (hC : C∈F) (f : SupportedIdeal→ℂ) :
    (∑D∈sourceDivisorUnion F W hW Y hY,sourceMobiusWeight W hW Y hY C D*f D)=
      ∑D∈sourceDivisors W hW Y hY C,(moebius D.val:ℂ)*f D := by
  rw [←Finset.sum_subset (show sourceDivisors W hW Y hY C⊆sourceDivisorUnion F W hW Y hY from
    fun D hD=>Finset.mem_biUnion.mpr ⟨C,hC,hD⟩) (by intro D hD hn;simp only [sourceMobiusWeight,ite_eq_right hn,zero_mul])]
  exact Finset.sum_congr rfl (fun D hD=>by rw [sourceMobiusWeight,ite_eq_left hD])

theorem originalCommonBlock_eq_rectangle (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (F : Finset SupportedIdeal) (C : SupportedIdeal) (hC : C∈F)
    (k : GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    originalCommonBlock S hS σ C k W hW Y Q hY U v=
      ∑D∈sourceDivisorUnion F W hW Y hY,sourceMobiusWeight W hW Y hY C D*
        canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
          ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/gramIdealNorm C))
          (Y/(gramIdealNorm C*gramIdealNorm D)) := by
  rw [sourceMobiusWeight_rectangle F W hW Y hY C hC]
  rw [originalCommonBlock_eq_lattice S hS hbad σ C k W hW Y Q hY hQ U v]
  rw [←sourceDivisors_sum W hW Y hY C]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  rw [frequencyScale_ratio]
  congr 1
  simp only [commonResidualScale,gramIdealNorm,div_div]

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1763

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramTruncation.lean; sha256: f671f7fe38580c6519f4eee470de91986b0ddaad8b51db167a42c8b75a283b72 -/
section Source1764
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def sourceTruncation (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (E : Finset GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  ((Q/Y^3:ℝ):ℂ)*∑C∈F,∑k∈E,originalCommonBlock S hS σ C k W hW Y Q hY U v

def sourceCanonicalSum (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (E : SupportedIdeal→Finset GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  ((Q/Y^3:ℝ):ℂ)*∑C∈F,∑D∈sourceDivisorUnion F W hW Y hY,sourceMobiusWeight W hW Y hY C D*
    ∑k∈E C,canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
      ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/gramIdealNorm C)) (Y/(gramIdealNorm C*gramIdealNorm D))

theorem sourceTruncation_eq_canonical (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (F : Finset SupportedIdeal) (E : Finset GramFrequency)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    sourceTruncation S hS σ F E W hW Y Q hY U v=sourceCanonicalSum S hS σ F (fun _=>E) W hW Y Q hY U v := by
  unfold sourceTruncation sourceCanonicalSum
  congr 1
  apply Finset.sum_congr rfl
  intro C hC
  simp_rw [originalCommonBlock_eq_rectangle S hS hbad σ F C hC _ W hW Y Q hY hQ U v]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun D hD=>(Finset.mul_sum ..).symm)

def exceptionalFrequencies (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (E : Finset GramFrequency) (C : SupportedIdeal) : Finset GramFrequency :=
  E.filter (ExceptionalFrequency S hS C)
def nonexceptionalFrequencies (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (E : Finset GramFrequency) (C : SupportedIdeal) : Finset GramFrequency :=
  E.filter (fun k=>¬ExceptionalFrequency S hS C k)

lemma sourceCanonicalSum_split (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (E : Finset GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    sourceCanonicalSum S hS σ F (fun _=>E) W hW Y Q hY U v=
      sourceCanonicalSum S hS σ F (exceptionalFrequencies S hS E) W hW Y Q hY U v+
      sourceCanonicalSum S hS σ F (nonexceptionalFrequencies S hS E) W hW Y Q hY U v := by
  unfold sourceCanonicalSum exceptionalFrequencies nonexceptionalFrequencies
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro C hC
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [←mul_add,Finset.sum_filter_add_sum_filter_not]

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1764

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramSourceEstimate.lean; sha256: 5d49b2ca1d93ac56c69c18a85fc61d3e90317cbf852d58626d691c67b05ad913 -/
section Source1765
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem original_source_truncation_bound (δ ε : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (hε : 0<ε) (hε1 : ε<1/6) (a b M₀ : ℝ) (ha : 0<a) (hab : a<b) (hM₀ : 0≤M₀)
    (W : ℝ→ℂ) (hcompact : HasCompactSupport W) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (hWM : ∀x,‖W x‖≤M₀) :
    ∃(J : ℕ)(H₁ H₂ : Finset (ℕ×ℕ))(K₁ K₂ : ℝ),0<K₁ ∧ 0<K₂ ∧
      ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→∀(σ : RayRing)
      (F : Finset SupportedIdeal)(E : Finset GramFrequency)(U : SchwartzMap ℝ ℂ)
      (v Y Q : ℝ)(hY : 0<Y),0<Q→
      ‖sourceTruncation S hS σ F E W hcompact Y Q hY U v‖≤
        K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*(Y^2/Q)*
          (Y/((Ideal.absNorm (jointFixedModulus S hS):ℝ)*(Y^2/Q)))^(-1+δ)+
        K₂*H₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*
          (Ideal.absNorm (jointFixedModulus S hS):ℝ)^ε*(Y^2/Q)^(1/6:ℝ) := by
  obtain ⟨J,H₁,hgood⟩ := canonical_nonexceptional_ideal_sum δ hδ hδ1 3 (by norm_num) a b ha hab
  obtain ⟨K₁,hK₁,hgood⟩ := hgood W hs hW
  obtain ⟨H₂,K₂,hK₂,hbadbound⟩ := canonical_exceptional_ideal_sum ε hε hε1 a b M₀ ha (by linarith) hM₀
  refine ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,?_⟩
  intro S hS hbad σ F E U v Y Q hY hQ
  let G:=sourceDivisorUnion F W hcompact Y hY
  have hα := fun (C : SupportedIdeal) (_ : C∈F) (D : SupportedIdeal) (_ : D∈G)=>sourceMobiusWeight_norm W hcompact Y hY C D
  have hg := hgood S hS σ F G (fun C _=>nonexceptionalFrequencies S hS E C)
    (sourceMobiusWeight W hcompact Y hY) hα
    (by intro C hC D hD k hk;exact (Finset.mem_filter.mp hk).2)
    U v (Y^2/Q) Y Q (by positivity) hY hQ.le
  have hb := hbadbound W hcompact hs hWM S hS σ F G (fun C _=>exceptionalFrequencies S hS E C)
    (sourceMobiusWeight W hcompact Y hY) hα
    (by intro C hC D hD k hk;exact (Finset.mem_filter.mp hk).2)
    U v (Y^2/Q) Y Q (by positivity) hY hQ.le
  rw [sourceTruncation_eq_canonical S hS hbad σ F E W hcompact Y Q hY hQ U v,sourceCanonicalSum_split]
  exact (norm_add_le _ _).trans ((add_le_add hb hg).trans_eq (add_comm _ _))

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1765

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramInfiniteEstimate.lean; sha256: 6b6f5bd3bdd4784362cd406b891fc50d0bf36549626a73cc5d7db554cfa256a5 -/
section Source1766
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff Topology
namespace SevenEighths.ProbeGramCommon
open Filter ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sourceTruncation_tendsto (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    Tendsto (fun E : Finset GramFrequency=>sourceTruncation S hS σ F E W hW Y Q hY U v) atTop
      (𝓝 (((Q/Y^3:ℝ):ℂ)*∑C∈F,∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v)) := by
  have hs (C : SupportedIdeal) : Summable (fun k : GramFrequency=>originalCommonBlock S hS σ C k W hW Y Q hY U v) :=
    originalCommonBlock_summable S hS σ C W hW Y Q hY hQ U v
  have hh := (summable_sum (s:=F) (fun C hC=>hs C)).hasSum.mul_left ((Q/Y^3:ℝ):ℂ)
  rw [Summable.tsum_finsetSum (fun C hC=>hs C)] at hh
  change Tendsto _ atTop (𝓝 _) at hh
  convert hh using 1
  funext E
  unfold sourceTruncation
  rw [←Finset.mul_sum,Finset.sum_comm]

theorem original_energy_nonzero_bound (δ ε : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (hε : 0<ε) (hε1 : ε<1/6) (a b M₀ : ℝ) (ha : 0<a) (hab : a<b) (hM₀ : 0≤M₀)
    (W : ℝ→ℂ) (hcompact : HasCompactSupport W) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (hWM : ∀x,‖W x‖≤M₀) :
    ∃(J : ℕ)(H₁ H₂ : Finset (ℕ×ℕ))(K₁ K₂ : ℝ),0<K₁ ∧ 0<K₂ ∧
      ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→∀(σ : RayRing)
      (U : SchwartzMap ℝ ℂ)(v Y Q : ℝ)(hY : 0<Y),0<Q→
      ‖gaussEnergy (lowGaussColumns W hcompact Y hY) (fun I=>primaryGenerator I.val)
        (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
        (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q-
        lowGramZeroMode (calibrationForSet S hS) W hcompact Y hY σ v U Q‖≤
        K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*(Y^2/Q)*
          (Y/((Ideal.absNorm (jointFixedModulus S hS):ℝ)*(Y^2/Q)))^(-1+δ)+
        K₂*H₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*
          (Ideal.absNorm (jointFixedModulus S hS):ℝ)^ε*(Y^2/Q)^(1/6:ℝ) := by
  obtain ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,hbound⟩ := original_source_truncation_bound δ ε hδ hδ1 hε hε1 a b M₀ ha hab hM₀ W hcompact hs hW hWM
  refine ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,?_⟩
  intro S hS hbad σ U v Y Q hY hQ
  rw [original_energy_common_blocks S hS σ W hcompact Y Q hY hQ U v,add_sub_cancel_left]
  exact le_of_tendsto (sourceTruncation_tendsto S hS σ _ W hcompact Y Q hY hQ U v).norm
    (Eventually.of_forall (fun E=>hbound S hS hbad σ _ E U v Y Q hY hQ))

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1766

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramScaleLoss.lean; sha256: aa6276fcde446984a64de421676498db551dd84f8bd190c5ddba4dd16898ac32 -/
section Source1767
namespace OAI

noncomputable section
namespace SevenEighths.ProbeGramCommon

lemma nonexceptional_scale_identity (M P Y δ : ℝ) (hM : 0<M) (hP : 0<P) (hY : 0<Y) :
    P*(Y/(M*P))^(-1+δ)=M^(1-δ)*P^(2-δ)*Y^(-1+δ) := by
  rw [Real.div_rpow hY.le (mul_pos hM hP).le,Real.mul_rpow hM.le hP.le,div_eq_mul_inv,mul_inv_rev,
    ←Real.rpow_neg hM.le,←Real.rpow_neg hP.le]
  have he : P*P^(-(-1+δ))=P^(2-δ) := by
    conv_lhs => lhs;rw [←Real.rpow_one P]
    rw [←Real.rpow_add hP]
    congr 1
    ring
  calc
    _=M^(1-δ)*(P*P^(-(-1+δ)))*Y^(-1+δ) := by rw [show -(-1+δ)=1-δ by ring];ring
    _=_ := by rw [he]

lemma nonexceptional_scale_loss (M P Y δ : ℝ) (hM : 1≤M) (hP : 1≤P) (hY : 0<Y)
    (hδ : 0≤δ) :
    P*(Y/(M*P))^(-1+δ)≤M*(P^2/Y)*Y^δ := by
  have hm : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hp : 0<P := lt_of_lt_of_le zero_lt_one hP
  rw [nonexceptional_scale_identity M P Y δ hm hp hY]
  have hmp : M^(1-δ)≤M := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM (show 1-δ≤1 by linarith)
  have hpp : P^(2-δ)≤P^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hP (show 2-δ≤2 by linarith)
  calc
    _≤M*P^2*Y^(-1+δ) := mul_le_mul_of_nonneg_right
      (mul_le_mul hmp hpp (by positivity) hm.le) (by positivity)
    _=_ := by rw [Real.rpow_add hY,Real.rpow_neg_one];ring

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1767

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramBound.lean; sha256: 589051b4b1a3666c2a0a60bf05760c4def5f8f5e2544ef3cd2775f94894f36dc -/
section Source1768
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentGaussEnergy EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem actual_additive_gram_bound (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (a b M₀ : ℝ) (ha : 0<a) (hab : a<b) (hM₀ : 0≤M₀)
    (W : ℝ→ℂ) (hcompact : HasCompactSupport W) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (hWM : ∀x,‖W x‖≤M₀) :
    ∃J : ℕ,∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→∀U : SchwartzMap ℝ ℂ,
    ∃K : ℝ,0<K ∧ ∀(σ : RayRing)(v Y Q : ℝ)(hY : 1≤Y),0<Q→1≤Y^2/Q→
      ‖gaussEnergy (lowGaussColumns W hcompact Y (lt_of_lt_of_le zero_lt_one hY))
        (fun I=>primaryGenerator I.val) (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
        (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q‖≤
      K*(1+|v|)^J*(Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ := by
  obtain ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,hbound⟩ := original_energy_nonzero_bound δ (1/12) hδ hδ1
    (by norm_num) (by norm_num) a b M₀ ha hab hM₀ W hcompact hs hW hWM
  obtain ⟨K₀,hK₀,hzero⟩ := lowGramZeroMode_source_bound a b M₀ ha hM₀
  refine ⟨J,?_⟩
  intro S hS hbad U
  let M : ℝ := Ideal.absNorm (jointFixedModulus S hS)
  have hM : 1≤M := by dsimp [M];exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (jointFixedModulus_nonzero S hS))
  let A₀ := K₀*‖paperRadialFourier U 0‖
  let A₁ := K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*M
  let A₂ := K₂*H₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*M^(1/12:ℝ)
  have hA₀ : 0≤A₀ := by dsimp [A₀];positivity
  have hA₁ : 0≤A₁ := by dsimp [A₁];positivity
  have hA₂ : 0≤A₂ := by dsimp [A₂];positivity
  refine ⟨1+A₀+A₁+A₂,by positivity,?_⟩
  intro σ v Y Q hY hQ hP
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  let P := Y^2/Q
  have hp : 1≤P := hP
  have hp0 : 0<P := lt_of_lt_of_le zero_lt_one hp
  let Z := lowGramZeroMode (calibrationForSet S hS) W hcompact Y hy σ v U Q
  let E := gaussEnergy (lowGaussColumns W hcompact Y hy) (fun I=>primaryGenerator I.val)
    (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
    (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q
  have hn := hbound S hS hbad σ U v Y Q hy hQ
  have hz : ‖Z‖≤A₀*(Q/Y) := by
    have hh := hzero S hS W hcompact hs hWM Y hY σ v U Q hQ.le
    convert hh using 1 ; dsimp [Z,A₀] ; ring
  have hgood : K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P*
      (Y/(M*P))^(-1+δ)≤A₁*(1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ := by
    have hh := mul_le_mul_of_nonneg_left (nonexceptional_scale_loss M P Y δ hM hp hy hδ.le)
      (show 0≤K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y) by positivity)
    convert hh using 1 <;> (try dsimp [A₁]) <;> ring
  have henergy : ‖E‖≤A₀*(Q/Y)+A₁*(1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ+A₂*(Q/Y)*P^(1/6:ℝ) := by
    have hn' : ‖E-Z‖≤A₁*(1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ+A₂*(Q/Y)*P^(1/6:ℝ) := by
      apply hn.trans
      exact add_le_add hgood (by dsimp [A₂,M,P];ring_nf;exact le_rfl)
    calc
      ‖E‖=‖(E-Z)+Z‖ := by congr 1;ring
      _≤‖E-Z‖+‖Z‖ := norm_add_le _ _
      _≤_ := by linarith
  let B := (1+|v|)^J*(Q/Y)*(1+P^(1/6:ℝ)+P^2/Y)*Y^δ
  have hb : 0≤B := by dsimp [B];positivity
  have hh : 1≤(1+|v|)^J := one_le_pow₀ (by linarith [abs_nonneg v])
  have hyd : 1≤Y^δ := Real.one_le_rpow hY hδ.le
  have hshape : 1≤1+P^(1/6:ℝ)+P^2/Y := by
    have hpow : 0≤P^(1/6:ℝ) := by positivity
    have hratio : 0≤P^2/Y := by positivity
    linarith
  have hb₀ : Q/Y≤B := by
    calc
      Q/Y=(1:ℝ)*(Q/Y)*1*1 := by ring
      _≤B := by dsimp [B];gcongr
  have hb₁ : (1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ≤B := by
    dsimp [B]
    gcongr
    have hpow : 0≤P^(1/6:ℝ) := by positivity
    linarith
  have hb₂ : (Q/Y)*P^(1/6:ℝ)≤B := by
    calc
      _=(1:ℝ)*(Q/Y)*P^(1/6:ℝ)*1 := by ring
      _≤B := by
        dsimp [B]
        gcongr
        have hratio : 0≤P^2/Y := by positivity
        linarith
  change ‖E‖≤_
  calc
    _≤A₀*(Q/Y)+A₁*((1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ)+A₂*((Q/Y)*P^(1/6:ℝ)) := by convert henergy using 1 ; ring
    _≤A₀*B+A₁*B+A₂*B := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hb₀ hA₀)
      (mul_le_mul_of_nonneg_left hb₁ hA₁)) (mul_le_mul_of_nonneg_left hb₂ hA₂)
    _≤(1+A₀+A₁+A₂)*B := by nlinarith
    _=_ := by dsimp [B,P];ring

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1768

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGramApplied.lean; sha256: 871f9f2475260271be5c50cca3d77134c21a3e75fa9431b47039edbe297900a6 -/
section Source1769
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem lowSeparatedIntegrand_actual_gram (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (a b M : ℝ) (ha : 0<a) (hab : a<b) (hM : 0≤M)
    (W1 : ℝ→ℂ) (hW1c : HasCompactSupport W1) (hW1 : Function.support W1⊆Set.Icc a b)
    (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (hb₀ : 0<b₀) :
    ∃J : ℕ,∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→
      ∃K : ℝ,0<K ∧ ∀(W0 : ℝ→ℂ)(X Y : ℝ)(hX : 0<X)(hY : 1≤Y)
        (B : RayRing→O→ℂ)(v : ℝ),1≤Y^2/lowPhysicalScale (calibrationForSet S hS) X Y→
      ‖lowSeparatedIntegrand (calibrationForSet S hS) W0 W1 (lowOuterCutoff a₀ b₀) X Y B v‖≤
        ‖mellin W0 ((v:ℂ)*Complex.I)‖*
        Real.sqrt (K*(1+|v|)^J*(lowPhysicalScale (calibrationForSet S hS) X Y/Y)*
          (1+(Y^2/lowPhysicalScale (calibrationForSet S hS) X Y)^(1/6:ℝ)+
            (Y^2/lowPhysicalScale (calibrationForSet S hS) X Y)^2/Y)*Y^δ)*
        ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a₀ b₀ ha₀ hb₀
          (lowPhysicalScale (calibrationForSet S hS) X Y)
          (lowPhysicalScale_pos _ X Y hX (lt_of_lt_of_le zero_lt_one hY)),‖B σ m‖^2) := by
  obtain ⟨J,hgram⟩ := ProbeGramCommon.actual_additive_gram_bound δ hδ hδ1 a b M ha hab hM
    W1 hW1c hW1 hW1s hWM
  refine ⟨J,?_⟩
  intro S hS hbad
  obtain ⟨K,hK,hgram⟩ := hgram S hS hbad (lowGaussMajorant a₀ b₀ ha₀ hb₀)
  refine ⟨K,hK,?_⟩
  intro W0 X Y hX hY B v hP
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  let Q := lowPhysicalScale (calibrationForSet S hS) X Y
  have hQ : 0<Q := lowPhysicalScale_pos _ X Y hX hy
  let A := K*(1+|v|)^J*(Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ
  have hbound (σ : RayRing) :
      (gaussEnergy (lowGaussColumns W1 hW1c Y hy) (fun I=>primaryGenerator I.val)
        (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
        (lowGaussColumn (calibrationForSet S hS) W1 Y σ v) (lowGaussMajorant a₀ b₀ ha₀ hb₀) Q).re≤A :=
    (Complex.re_le_norm _).trans (hgram σ v Y Q hY hQ hP)
  apply (lowSeparatedIntegrand_actual_energies a₀ b₀ ha₀ hb₀ (calibrationForSet S hS)
    W0 W1 hW1c X Y hX hy B v).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _≤∑σ : RayRing,Real.sqrt A*Real.sqrt (∑m∈lowNumeratorRows a₀ b₀ ha₀ hb₀ Q hQ,‖B σ m‖^2) :=
      Finset.sum_le_sum (fun σ _=>mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hbound σ)) (Real.sqrt_nonneg _))
    _=_ := (Finset.mul_sum ..).symm

end SevenEighths.ProbePhysical
end

end OAI

end Source1769

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGramScale.lean; sha256: ca46b12dad51371b9b2c15393d6aa5d5a1d6c0586a2402ebc5bf7332e7435e90 -/
section Source1770
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma compensated_gram_ratio (q X Y L : ℝ) (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hL : 0<L) :
    (Y/L)^2/(q*(X/L)*(Y/L))=Y/(q*X) := by
  field_simp

lemma compensated_gram_scale_bound (q X Y L δ : ℝ)
    (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hL : 1≤L) (hδ : 0≤δ)
    (hP : q*X≤Y) (htail : L*Y≤q^2*X^2) :
    (q*(X/L)*(Y/L)/(Y/L))*
      (1+((Y/L)^2/(q*(X/L)*(Y/L)))^(1/6:ℝ)+
        ((Y/L)^2/(q*(X/L)*(Y/L)))^2/(Y/L))*(Y/L)^δ ≤
      3*(q*X/L)*(Y/(q*X))^(1/6:ℝ)*Y^δ := by
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hp : 1≤Y/(q*X) := (le_div_iff₀ (mul_pos hq hX)).mpr (by simpa using hP)
  have hr : 1≤(Y/(q*X))^(1/6:ℝ) := Real.one_le_rpow hp (by norm_num)
  have ht : (Y/(q*X))^2/(Y/L)≤1 := by
    have he : (Y/(q*X))^2/(Y/L)=L*Y/(q^2*X^2) := by field_simp
    rw [he]
    exact (div_le_one (by positivity)).mpr htail
  have hys : (Y/L)^δ≤Y^δ := Real.rpow_le_rpow (by positivity)
    ((div_le_self hY.le hL)) hδ
  rw [compensated_gram_ratio q X Y L hq hX hY hl]
  have he : q*(X/L)*(Y/L)/(Y/L)=q*X/L := by field_simp
  rw [he]
  calc
    _≤(q*X/L)*(3*(Y/(q*X))^(1/6:ℝ))*Y^δ :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hys
        (by positivity) (by positivity)
    _=_ := by ring

lemma source_gram_power (Z δ : ℝ) (hZ : 0<Z) :
    Z^(17/48:ℝ)*(Z^(1/8:ℝ))^(1/6:ℝ)*(Z^(23/48:ℝ))^δ=
      Z^(3/8+(23/48)*δ:ℝ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma source_gram_sqrt_power (Z δ : ℝ) (hZ : 0<Z) :
    Real.sqrt (Z^(3/8+(23/48)*δ:ℝ))=Z^(3/16+(23/96)*δ:ℝ) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1770

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGramIntegrated.lean; sha256: 0749a6bbfffa1b4717a81ff44abd54e2f21eba5a1538515e8810b8b0d8d7eaf1 -/
section Source1771
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_mellin_sqrt_weight_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (hWs : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃C : ℝ,0<C ∧ ∀v : ℝ,
      ‖mellin W ((v:ℂ)*Complex.I)‖*Real.sqrt ((1+|v|)^J)≤C/(1+v^2) := by
  obtain ⟨C,hC,hb⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W a b ha hW hWs 0 0 (J+2)
  refine ⟨C,hC,?_⟩
  intro v
  apply CubicReflectionKernel.weighted_two_to_cauchy (by positivity) v
  have hp : 1≤(1+|v|)^J := one_le_pow₀ (by linarith [abs_nonneg v])
  have hs : Real.sqrt ((1+|v|)^J)≤(1+|v|)^J := Real.sqrt_le_self_iff.mpr (Or.inr hp)
  have hb' := hb 0 (by simp) v
  simp only [Complex.ofReal_zero,zero_add] at hb'
  calc
    _≤(1+|v|)^2*(‖mellin W ((v:ℂ)*Complex.I)‖*(1+|v|)^J) := by gcongr
    _=(1+|v|)^(J+2)*‖mellin W ((v:ℂ)*Complex.I)‖ := by rw [pow_add];ring
    _≤C := hb'

theorem lowSeparatedIntegral_actual_gram (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (a b M : ℝ) (ha : 0<a) (hab : a<b) (hM : 0≤M)
    (W1 : ℝ→ℂ) (hW1c : HasCompactSupport W1) (hW1 : Function.support W1⊆Set.Icc a b)
    (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (hb₀ : 0<b₀)
    (W0 : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW0s : ContDiff ℝ ∞ W0) :
    ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→
      ∃C : ℝ,0<C ∧ ∀(X Y : ℝ)(hX : 0<X)(hY : 1≤Y)(B : RayRing→O→ℂ),
        1≤Y^2/lowPhysicalScale (calibrationForSet S hS) X Y→
      ‖∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
        (lowOuterCutoff a₀ b₀) X Y B v‖≤
        C*Real.sqrt ((lowPhysicalScale (calibrationForSet S hS) X Y/Y)*
          (1+(Y^2/lowPhysicalScale (calibrationForSet S hS) X Y)^(1/6:ℝ)+
            (Y^2/lowPhysicalScale (calibrationForSet S hS) X Y)^2/Y)*Y^δ)*
        ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a₀ b₀ ha₀ hb₀
          (lowPhysicalScale (calibrationForSet S hS) X Y)
          (lowPhysicalScale_pos _ X Y hX (lt_of_lt_of_le zero_lt_one hY)),‖B σ m‖^2) := by
  obtain ⟨J,hgram⟩ := lowSeparatedIntegrand_actual_gram δ hδ hδ1 a b M ha hab hM W1 hW1c hW1 hW1s hWM a₀ b₀ ha₀ hb₀
  obtain ⟨CM,hCM,hm⟩ := low_mellin_sqrt_weight_bound W0 a0 b0 ha0 hW0 hW0s J
  intro S hS hbad
  obtain ⟨K,hK,hgram⟩ := hgram S hS hbad
  refine ⟨CM*Real.sqrt K*Real.pi,by positivity,?_⟩
  intro X Y hX hY B hP
  let Q := lowPhysicalScale (calibrationForSet S hS) X Y
  have hQ : 0<Q := lowPhysicalScale_pos _ X Y hX (lt_of_lt_of_le zero_lt_one hY)
  let A := (Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ
  have hA : 0≤A := by dsimp [A]; positivity
  let E := ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a₀ b₀ ha₀ hb₀ Q hQ,‖B σ m‖^2)
  have hE : 0≤E := Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _)
  have hh (v : ℝ) : ‖lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
      (lowOuterCutoff a₀ b₀) X Y B v‖≤(CM*Real.sqrt K*Real.sqrt A*E)*(1+v^2)⁻¹ := by
    have hg := hgram W0 X Y hX hY B v hP
    have he : K*(1+|v|)^J*(Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ=
        (1+|v|)^J*(K*A) := by dsimp [A];ring
    rw [he,Real.sqrt_mul (by positivity),Real.sqrt_mul hK.le] at hg
    calc
      _≤(‖mellin W0 ((v:ℂ)*Complex.I)‖*Real.sqrt ((1+|v|)^J))*
          (Real.sqrt K*Real.sqrt A*E) := by convert hg using 1 ;ring
      _≤(CM/(1+v^2))*(Real.sqrt K*Real.sqrt A*E) :=
        mul_le_mul_of_nonneg_right (hm v) (by positivity)
      _=_ := by rw [div_eq_mul_inv];ring
  have hi := norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul
    (CM*Real.sqrt K*Real.sqrt A*E)) (Filter.Eventually.of_forall hh)
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hi
  convert hi using 1 ;ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1771

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowTupleGram.lean; sha256: d3235add8c39a0637cb6fbcb55dc270c2456c2c6c031df4449b5eb5ab5c890a8 -/
section Source1772
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramFactor (C : CalibrationData) (X Y δ : ℝ) : ℝ :=
  Real.sqrt ((lowPhysicalScale C X Y/Y)*(1+(Y^2/lowPhysicalScale C X Y)^(1/6:ℝ)+
    (Y^2/lowPhysicalScale C X Y)^2/Y)*Y^δ)

def lowInverseMass (C : CalibrationData) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) : ℝ :=
  ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a b ha hb (lowPhysicalScale C X Y)
    (lowPhysicalScale_pos C X Y hX hY),‖B σ m‖^2)

lemma lowInverseMass_nonneg (C : CalibrationData) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) :
    0≤lowInverseMass C a b ha hb X Y hX hY B :=
  Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _)

lemma low_mellin_normalizer_norm (Q : ℝ) (_hQ : 0<Q) :
    ‖(Real.sqrt Q:ℂ)⁻¹*(1/(2*Real.pi):ℂ)‖=(Real.sqrt Q)⁻¹/(2*Real.pi) := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [norm_div,norm_one,norm_mul]
  norm_num [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  ring

theorem compensation_tuple_actual_gram (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→
    ∃C : ℝ,0<C ∧ ∀(K : ℕ)(η : HeckeFamily.Character)(slots : Fin K→Finset O)
      (hslots : ∀i x,x∈slots i→x≠0)(J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ)
      (X Y T t : ℝ)(hX : 0<X)(hY : 0<Y)(_hT : 0<T),
      (∀a : LowUnselectedTuple slots J,1≤Y/elementNorm (∏i : J,(a i).val))→
      (∀a : LowUnselectedTuple slots J,
        1≤(Y/elementNorm (∏i : J,(a i).val))^2/
          lowPhysicalScale (calibrationForSet S hS) (X/elementNorm (∏i : J,(a i).val))
            (Y/elementNorm (∏i : J,(a i).val)))→
      ‖∑p : (∀i,↥(slots i)),compensationSubsetWeight η W P (fun i=>(p i).val) J*
        compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J X Y T t*
          selectedSlotFactor W P (fun i=>(p i).val) J t‖≤
      C*∑a : LowUnselectedTuple slots J,
        ‖lowUnselectedWeight slots J W P a‖*
        ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))))⁻¹/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS)
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val)) δ*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1))
          (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (div_pos hX (lowUnselectedProduct_norm_pos slots hslots J a))
          (div_pos hY (lowUnselectedProduct_norm_pos slots hslots J a))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W P t)
            η S hS (lowSelectedIdeal slots J) T t) := by
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  intro S hS hbad
  obtain ⟨C,hC,hgram⟩ := lowSeparatedIntegral_actual_gram δ hδ hδ1 a1 b1 M ha1 hab1 hM
    W1 hW1c hW1 hW1s hWM (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) W0 a0 b0 ha0 hW0 hW0s S hS hbad
  refine ⟨C,hC,?_⟩
  intro K η slots hslots J W P X Y T t hX hY hT hYs hPs
  rw [compensation_tuple_low_polynomial η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hW0s
    slots hslots J W P X Y T t hX hY hT]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hL := lowUnselectedProduct_norm_pos slots hslots J a
  have hh := hgram (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
    (div_pos hX hL) (hYs a)
    (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W P t)
      η S hS (lowSelectedIdeal slots J) T t) (hPs a)
  rw [norm_mul,norm_mul,low_mellin_normalizer_norm _ (lowPhysicalScale_pos _ _ _ (div_pos hX hL) (div_pos hY hL))]
  calc
    _≤‖lowUnselectedWeight slots J W P a‖*
      ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))))⁻¹/(2*Real.pi))*
      (C*lowGramFactor (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val)) δ*
      lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1))
        (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
        (div_pos hX hL) (div_pos hY hL) _) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _=_ := by ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1772

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalCrudeMass.lean; sha256: 24664fd23cc50756de05eeb3912a5984b9b781d0661387b60324a7626286d222 -/
section Source1773
namespace OAI

noncomputable section
open scoped Classical
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ConcreteTraceCRT CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma calibration_elementNorm_ge_one (C : CalibrationData) : 1≤elementNorm C.generator := by
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))

lemma sexticGauss_norm_le (s : O) (hs : s≠0) (m : O) : ‖sexticGauss s hs m‖≤elementNorm s := by
  let := finite_quotient_span hs
  let : Fintype (O⧸Ideal.span {s}) := Fintype.ofFinite _
  rw [sexticGauss,tsum_fintype]
  calc
    _ ≤ ∑d : O⧸Ideal.span {s},‖idealRowHom (GaussianShiftedPartition.representative s d) (Ideal.span {s})*
      quotientTrace s hs (Ideal.Quotient.mk _ m*d)‖ := norm_sum_le _ _
    _ ≤ ∑_d : O⧸Ideal.span {s},(1:ℝ) := Finset.sum_le_sum (fun d _=>by
      rw [norm_mul,(quotientTrace s hs).norm_apply,mul_one]
      exact idealRowHom_norm _ _)
    _ = _ := by simp [elementNorm,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

lemma physicalRowWeight_arithmetic_form (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      (Y:ℂ)⁻¹*W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*lowArithmeticCoefficient C r.1*
        (Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X):ℂ)⁻¹*
        C.residueMonoid r.2*(Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
        sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)*
        W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)) := by
  unfold physicalRowWeight lowArithmeticCoefficient
  split_ifs <;> simp only [mul_zero,zero_mul]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma physicalRowWeight_crude_point (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (B0 B1 : ℝ) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : ∀x,‖W0 x‖≤B0) (hW1 : ∀x,‖W1 x‖≤B1)
    (X Y : ℝ) (hX : 1≤X) (hY : 0<Y) (r : PhysicalRowIndex) :
    ‖physicalRowWeight C W0 W1 X Y r‖≤B0*B1*‖C.tau‖⁻¹/Y := by
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  have hb := calibration_elementNorm_ge_one C
  have hscale : 0<elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X :=
    physicalRowScale_pos C X (lt_of_lt_of_le zero_lt_one hX) r.1
  have hqscale : (Ideal.absNorm r.1.val:ℝ)≤elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X := by
    have hbx : 1≤elementNorm C.generator*X := one_le_mul_of_one_le_of_one_le hb hX
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hqscale
  have hrad : (Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
      (Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)≤1 := by
    have hspos : 0<Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)*
      Real.sqrt (Ideal.absNorm r.1.val:ℝ) := mul_pos (Real.sqrt_pos.mpr hscale) (Real.sqrt_pos.mpr hq)
    calc
      _ = (Ideal.absNorm r.1.val:ℝ)/(Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)*
        Real.sqrt (Ideal.absNorm r.1.val:ℝ)) := by simp only [div_eq_mul_inv,mul_inv_rev];ring
      _ ≤ 1 := (div_le_one hspos).mpr (by nlinarith [mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (Ideal.absNorm r.1.val:ℝ)), Real.sq_sqrt hq.le])
  have hg := sexticGauss_norm_le (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)
  have he := (primaryGenerator_spec r.1.val (supported_primaryGenerator_ne_zero r.1.val r.1.property)).1
  unfold elementNorm at hg
  rw [he] at hg
  rw [physicalRowWeight_arithmetic_form]
  simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Y⁻¹*B1*‖C.tau‖⁻¹*(Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
      1*(Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)*B0 := by
      gcongr
      · exact hW1 _
      · exact lowArithmeticCoefficient_norm C r.1
      · exact C.residueMonoid_norm_le_one r.2
      · exact hW0 _
    _ = (B0*B1*‖C.tau‖⁻¹/Y)*((Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
        (Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hrad

lemma lowNumeratorRows_card (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 1≤Q) :
    ((lowNumeratorRows a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ)).card:ℝ)≤256*max 1 b*Q := by
  have hscale : 1≤2*max 1 b*Q := by nlinarith [le_max_left 1 b]
  have hh := DescentFiberCost.finite_element_count_real (lowNumeratorRows a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ)) _ hscale
    (by
      intro m hm
      have h := (lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ) m).mp hm)).2
      have hn := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hQ)).mp h
      rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      change elementNorm m≤2*max 1 b*Q
      exact hn.trans (by gcongr;exact le_max_right _ _))
  convert hh using 1 ; ring

lemma lowPhysicalScale_ge_one (C : CalibrationData) (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    1≤lowPhysicalScale C X Y :=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (calibration_elementNorm_ge_one C) hX) hY

lemma physicalRowWeight_source_rectangle (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW1c : HasCompactSupport W1) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : PhysicalRowIndex)
    (hr : r∉(lowGaussColumns W1 hW1c Y hY) ×ˢ
      (lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY))) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  by_cases hs : r.1∈lowGaussColumns W1 hW1c Y hY
  · have hm : r.2∉lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY) := fun hm=>hr (Finset.mem_product.mpr ⟨hs,hm⟩)
    have hz : lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (elementNorm r.2/lowPhysicalScale C X Y)=0 := by
      simpa only [lowNumeratorRows_mem,not_not] using hm
    rw [physicalRowWeight_insert_cutoff C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hY r]
    change lowOuterCutoff _ _ (elementNorm r.2/lowPhysicalScale C X Y)*_=0
    rw [hz,zero_mul]
  · apply physicalRowWeight_outer_zero
    simpa only [lowGaussColumns_mem,not_not] using hs

theorem physicalRowWeight_source_mass (a0 b0 a1 b1 B0 B1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,∀_hW1c : HasCompactSupport W1,
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀X Y : ℝ,1≤X → 1≤Y →
      (∑'r : PhysicalRowIndex,‖physicalRowWeight (calibrationForSet S hS) W0 W1 X Y r‖)≤
        K*lowPhysicalScale (calibrationForSet S hS) X Y := by
  let K := 32768*max 1 b1*max 1 (b0*b1)*B0*B1+1
  refine ⟨K,by dsimp only [K];positivity,?_⟩
  intro S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 X Y hX hY
  let C := calibrationForSet S hS
  have hx : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  let Q := lowPhysicalScale C X Y
  have hQ : 1≤Q := lowPhysicalScale_ge_one C X Y hX hY
  let F := lowGaussColumns W1 hW1c Y hy
  let R := lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) Q (lowPhysicalScale_pos C X Y hx hy)
  have hzero (r : PhysicalRowIndex) (hr : r∉F×ˢR) : ‖physicalRowWeight C W0 W1 X Y r‖=0 := by
    rw [physicalRowWeight_source_rectangle C W0 W1 hW1c a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hx hy r hr,norm_zero]
  have hpoint (r : PhysicalRowIndex) : ‖physicalRowWeight C W0 W1 X Y r‖≤B0*B1/Y := by
    have h := physicalRowWeight_crude_point C W0 W1 B0 B1 hB0 hB1 hWB0 hWB1 X Y hX hy r
    simpa only [C,calibrationForSet_tau_norm,inv_one,mul_one] using h
  have hF : (F.card:ℝ)≤128*max 1 b1*Y := lowGaussColumns_card W1 hW1c Y hY a1 b1 hW1
  have hR : (R.card:ℝ)≤256*max 1 (b0*b1)*Q := by
    simpa only [R,max_eq_right (le_max_left 1 (b0*b1))] using lowNumeratorRows_card (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) Q hQ
  rw [tsum_eq_sum (s:=F×ˢR) hzero]
  calc
    _ ≤ ∑_r∈F×ˢR,B0*B1/Y := Finset.sum_le_sum (fun r _=>hpoint r)
    _ = (F.card:ℝ)*(R.card:ℝ)*(B0*B1/Y) := by simp [Finset.card_product,mul_assoc]
    _ ≤ (128*max 1 b1*Y)*(256*max 1 (b0*b1)*Q)*(B0*B1/Y) := by gcongr
    _ = (32768*max 1 b1*max 1 (b0*b1)*B0*B1)*Q := by field_simp;ring
    _ ≤ K*Q := mul_le_mul_of_nonneg_right (by dsimp only [K];linarith) (le_trans zero_le_one hQ)

end SevenEighths.ProbePhysical
end

end OAI

end Source1773

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowSourceScales.lean; sha256: 6151ef7adff228aba72f9c7b85eab4d31a7ac3d76d85cd156227a4e935e94de2 -/
section Source1774
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma source_scale_ratio (Z : ℝ) (hZ : 0<Z) :
    Z^(23/48:ℝ)/Z^(17/48:ℝ)=Z^(1/8:ℝ) := by
  rw [←Real.rpow_sub hZ]
  norm_num

lemma source_scale_square (Z : ℝ) (hZ : 0<Z) :
    Z^(11/48:ℝ)*Z^(23/48:ℝ)=(Z^(17/48:ℝ))^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  norm_num

lemma source_compensated_scale_admissible (q Z L : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(1/8:ℝ)) (hLl : L≤Z^(11/48:ℝ)) :
    1≤Z^(23/48:ℝ)/L ∧
    q*Z^(17/48:ℝ)≤Z^(23/48:ℝ) ∧
    L*Z^(23/48:ℝ)≤q^2*(Z^(17/48:ℝ))^2 := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show (11/48:ℝ)≤23/48 by norm_num))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (17/48))).mp
    rwa [source_scale_ratio Z hz]
  · calc
      _≤Z^(11/48:ℝ)*Z^(23/48:ℝ) := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(17/48:ℝ))^2 := source_scale_square Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma source_compensated_gram_scale (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(1/8:ℝ)) (hLl : L≤Z^(11/48:ℝ)) (hδ : 0≤δ) :
    (q*(Z^(17/48:ℝ)/L)*(Z^(23/48:ℝ)/L)/(Z^(23/48:ℝ)/L))*
      (1+((Z^(23/48:ℝ)/L)^2/(q*(Z^(17/48:ℝ)/L)*(Z^(23/48:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(23/48:ℝ)/L)^2/(q*(Z^(17/48:ℝ)/L)*(Z^(23/48:ℝ)/L)))^2/(Z^(23/48:ℝ)/L))*
      (Z^(23/48:ℝ)/L)^δ ≤
        (3*q/L)*Z^(3/8+(23/48)*δ:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := source_compensated_scale_admissible q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^(23/48:ℝ)/(q*Z^(17/48:ℝ))≤Z^(1/8:ℝ) := by
    rw [←source_scale_ratio Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤Z^(23/48:ℝ)/(q*Z^(17/48:ℝ))) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^(17/48:ℝ)/L)*(Z^(1/8:ℝ))^(1/6:ℝ)*(Z^(23/48:ℝ))^δ := by gcongr
    _=(3*q/L)*(Z^(17/48:ℝ)*(Z^(1/8:ℝ))^(1/6:ℝ)*(Z^(23/48:ℝ))^δ) := by ring
    _=_ := by rw [source_gram_power Z δ hz]

lemma source_compensated_gram_sqrt (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(1/8:ℝ)) (hLl : L≤Z^(11/48:ℝ)) (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^(17/48:ℝ)/L)*(Z^(23/48:ℝ)/L)/(Z^(23/48:ℝ)/L))*
      (1+((Z^(23/48:ℝ)/L)^2/(q*(Z^(17/48:ℝ)/L)*(Z^(23/48:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(23/48:ℝ)/L)^2/(q*(Z^(17/48:ℝ)/L)*(Z^(23/48:ℝ)/L)))^2/(Z^(23/48:ℝ)/L))*
      (Z^(23/48:ℝ)/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^(3/16+(23/96)*δ:ℝ) := by
  apply (Real.sqrt_le_sqrt (source_compensated_gram_scale q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),source_gram_sqrt_power Z δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma lowGramFactor_source_bound (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤Z)
    (hL : 1≤L) (hql : elementNorm C.generator≤Z^(1/8:ℝ))
    (hLl : L≤Z^(11/48:ℝ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^(3/16+(23/96)*δ:ℝ) :=
  source_compensated_gram_sqrt _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ

lemma eventually_compensated_source_scales (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧ elementNorm C.generator≤Z^(1/8:ℝ) ∧
      ∀L : ℝ,1≤L→L≤B*Z^(1/6:ℝ)→
        1≤Z^(23/48:ℝ)/L ∧
        1≤(Z^(23/48:ℝ)/L)^2/lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^(3/16+(23/96)*δ:ℝ) := by
  have hq := (tendsto_rpow_atTop (show 0<(1/8:ℝ) by norm_num)).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<(1/16:ℝ) by norm_num)).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤Z^(11/48:ℝ) := calc
    L≤B*Z^(1/6:ℝ) := hLB
    _≤Z^(1/16:ℝ)*Z^(1/6:ℝ) := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^(11/48:ℝ) := by rw [←Real.rpow_add hz];norm_num
  obtain ⟨hy,hp,_⟩ := source_compensated_scale_admissible _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=>lowGramFactor_source_bound C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

end SevenEighths.ProbePhysical
end

end OAI

end Source1774

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowSlotScales.lean; sha256: 31f477ed5ee42505a53ea82aea9f7f982933f4ac4386adb232e82ad402e7fc3a -/
section Source1775
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma elementNorm_finset_prod {ι : Type*} (F : Finset ι) (p : ι→O) :
    elementNorm (∏i∈F,p i)=∏i∈F,elementNorm (p i) := by
  induction F using Finset.induction_on with
  | empty => simp [elementNorm_one]
  | @insert i F hi ih => simp only [Finset.prod_insert hi,elementNorm_mul,ih]

lemma lowUnselectedProduct_norm_ge_one {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    1≤elementNorm (∏i : J,(a i).val) := by
  have hn : (∏i : J,(a i).val)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hslots i.val _ (a i).property)
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hn))

lemma lowUnselectedProduct_norm_bound {K : ℕ} (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (b Z : ℝ) (hb : 1≤b) (hZ : 1≤Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(a i).val)≤b^K*Z^(1/6:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑i∈J,ell i≤1/6 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hell i)).trans hsum
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,b*Z^(ell i.val) := Finset.prod_le_prod₀ (fun _ _=>by unfold elementNorm;positivity)
      (fun i _=>hslots i.val _ (a i).property)
    _=b^J.card*Z^(∑i∈J,ell i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hz,Finset.sum_coe_sort]
    _≤b^K*Z^(1/6:ℝ) := mul_le_mul (pow_le_pow_right₀ hb hc)
      (Real.rpow_le_rpow_of_exponent_le hZ hsub) (by positivity) (by positivity)

theorem eventually_original_slot_scales {K : ℕ} (C : CalibrationData) (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6) (b : ℝ) (hb : 1≤b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      ∀(slots : Fin K→Finset O)(_hslots : ∀i x,x∈slots i→x≠0),
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(a : LowUnselectedTuple slots J),
      let L := elementNorm (∏i : J,(a i).val)
      1≤Z^(23/48:ℝ)/L ∧
      1≤(Z^(23/48:ℝ)/L)^2/lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm C.generator/L)*Z^(3/16+(23/96)*δ:ℝ) := by
  filter_upwards [eventually_compensated_source_scales C (b^K)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro slots hslots hnorm J a
  exact hZ.2.2 _ (lowUnselectedProduct_norm_ge_one slots hslots J a)
    (lowUnselectedProduct_norm_bound ell hell hsum b Z hb hZ.1 slots hnorm J a)

end SevenEighths.ProbePhysical
end

end OAI

end Source1775

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowOriginalPools.lean; sha256: a60bcbebdc46f6d24901d4e9a510d803ef52bf1f04c832885e6f348517820efe -/
section Source1776
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma originalPool_element_norm (R : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b Y : ℝ) (ha : 0≤a) (hab : a≤b) (hY : 0<Y) (n : O)
    (hn : n∈canonicalSlotSupport (pool R S a b Y)) : elementNorm n≤Y*b := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
  rw [primaryTuple_norm P (pool_supported R S hS a b Y P hP)]
  exact (pool_norm_bounds R S ha hab hY P hP).2

theorem originalPools_low_scales {K : ℕ} (R : Set Id) (S : Finset Id)
    (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      let T := fun i=>canonicalSlotSupport (pool R S a b (Z^(ell i)))
      ∀(J : Finset (Fin K))(p : LowUnselectedTuple T J),
      let L := elementNorm (∏i : J,(p i).val)
      1≤Z^(23/48:ℝ)/L ∧
      1≤(Z^(23/48:ℝ)/L)^2/lowPhysicalScale (calibrationForSet S hmax) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor (calibrationForSet S hmax) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm (calibrationForSet S hmax).generator/L)*Z^(3/16+(23/96)*δ:ℝ) := by
  filter_upwards [eventually_original_slot_scales (calibrationForSet S hmax) ell hell hsum
    (max 1 b) (le_max_left _ _)] with Z hZ
  refine ⟨hZ.1,?_⟩
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ.1
  apply hZ.2
  · intro i n hn
    exact canonicalSlotSupport_nonzero _ (pool_supported R S hS a b _) n hn
  · intro i n hn
    apply (originalPool_element_norm R S hS a b (Z^(ell i)) ha hab (by positivity) n hn).trans
    calc
      _≤Z^(ell i)*max 1 b := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _=_ := mul_comm _ _

end SevenEighths.ProbePhysical
end

end OAI

end Source1776

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowNominalGeometry.lean; sha256: 83f5fbf5452eed0fef0955a2a8da86a08060ffdcd16d7c9736159dd88e77064d -/
section Source1777
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowUnselectedLength {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) : ℝ := ∑i∈J,ell i

def lowSelectedLength {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) : ℝ := ∑i : SelectedSlot J,ell i.val

lemma lowLength_sum {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) :
    lowUnselectedLength ell J+lowSelectedLength ell J=∑i,ell i := by
  rw [lowUnselectedLength,lowSelectedLength,Finset.sum_coe_sort]
  exact Finset.sum_add_sum_compl J ell

lemma lowLength_bounds {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤1/6) (J : Finset (Fin K)) :
    0≤lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤1/6 ∧
    0≤lowSelectedLength ell J ∧ lowSelectedLength ell J≤1/6-lowUnselectedLength ell J := by
  have hu : 0≤lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma lowUnselectedProduct_norm_lower {K : ℕ} (ell : Fin K→ℝ)
    (a Z : ℝ) (ha : 0<a) (hZ : 0<Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→a*Z^(ell i)≤elementNorm x)
    (J : Finset (Fin K)) (p : LowUnselectedTuple slots J) :
    (min 1 a)^K*Z^(lowUnselectedLength ell J)≤elementNorm (∏i : J,(p i).val) := by
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤a^J.card*Z^(lowUnselectedLength ell J) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (pow_le_pow_of_le_one (le_of_lt (lt_min zero_lt_one ha)) (min_le_left _ _) hc).trans
        (pow_le_pow_left₀ (by positivity) (min_le_right _ _) _)
    _=∏i : J,a*Z^(ell i.val) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ,Finset.sum_coe_sort]
      rfl
    _≤_ := Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun i _=>hslots i.val _ (p i).property)

lemma originalPool_element_lower (R : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b Y : ℝ) (ha : 0≤a) (hab : a≤b) (hY : 0<Y) (n : O)
    (hn : n∈canonicalSlotSupport (pool R S a b Y)) : a*Y≤elementNorm n := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
  rw [primaryTuple_norm P (pool_supported R S hS a b Y P hP)]
  simpa only [mul_comm] using (pool_norm_bounds R S ha hab hY P hP).1.le

lemma lowPhysicalScale_source (C : CalibrationData) (Z L : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)=
      elementNorm C.generator*Z^(5/6:ℝ)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(17/48:ℝ)*Z^(23/48:ℝ)=Z^(5/6:ℝ) := by rw [←Real.rpow_add hZ];norm_num
  rw [←he]
  ring

lemma lowPhysicalScale_nominal_bound (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0<Z) (hc : 0<c) (hL : c*Z^d≤L) :
    lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)≤
      (elementNorm C.generator/c^2)*Z^(5/6-2*d:ℝ) := by
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  rw [lowPhysicalScale_source C Z L hZ]
  calc
    _≤elementNorm C.generator*Z^(5/6:ℝ)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ]
      ring

lemma lowSelectedScale_product {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0<Z) :
    (∏i∈Finset.univ\J,Z^(ell i))=Z^(lowSelectedLength ell J) := by
  rw [lowSelectedLength,Finset.sum_coe_sort,Real.rpow_sum_of_pos hZ]

lemma lowSelectedCaps_product {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (J : Finset (Fin K)) (Z b : ℝ) (hZ : 1≤Z) :
    (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤
      (max 1 b)^K*Z^(lowSelectedLength ell J) := by
  have hc : Fintype.card (SelectedSlot J)≤K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  calc
    _≤∏i : SelectedSlot J,max 1 b*Z^(ell i.val) := by
      apply Finset.prod_le_prod₀ (fun _ _=>le_trans zero_le_one (le_max_left _ _))
      intro i hi
      apply max_le
      · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i.val))
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _=(max 1 b)^(Fintype.card (SelectedSlot J))*Z^(lowSelectedLength ell J) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
      rfl
    _≤_ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) hc) (by positivity)

end SevenEighths.ProbePhysical
end

end OAI

end Source1777

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowCentralGeometry.lean; sha256: c2b8de59af37fc88f509f02fdcf6608f1b91c848dbe1a5b74b83b1eb70850ef4 -/
section Source1778
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical

lemma lowUnselectedProduct_norm_upper_nominal {K : ℕ} (ell : Fin K→ℝ)
    (b Z : ℝ) (hZ : 0<Z) (slots : Fin K→Finset ActualEisensteinCubic.O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (p : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(p i).val)≤(max 1 b)^K*Z^(lowUnselectedLength ell J) := by
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,max 1 b*Z^(ell i.val) := Finset.prod_le_prod₀
      (fun _ _=>by unfold elementNorm;positivity)
      (fun i _=>(hslots i.val _ (p i).property).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    _=(max 1 b)^J.card*Z^(lowUnselectedLength ell J) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ,Finset.sum_coe_sort]
      rfl
    _≤_ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) hc) (by positivity)

theorem eventually_low_selected_caps {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (b ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧ ∀J : Finset (Fin K),
      (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤Z^(lowSelectedLength ell J+ε/2) := by
  have hp : 0<ε/2 := by linarith
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hp).eventually (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro J
  apply (lowSelectedCaps_product ell hell J Z b hZ.le).trans
  calc
    _≤Z^(ε/2)*Z^(lowSelectedLength ell J) := mul_le_mul_of_nonneg_right hc (by positivity)
    _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)];congr 1;ring

def lowCentralShift (Z T ell0 : ℝ) : ℝ := Real.logb Z T-1-ell0

lemma lowCentralShift_scale (Z T ell0 : ℝ) (hZ : 1<Z) (hT : 0<T) :
    Z^(1+ell0+lowCentralShift Z T ell0)=T := by
  rw [lowCentralShift,show 1+ell0+(Real.logb Z T-1-ell0)=Real.logb Z T by ring]
  exact Real.rpow_logb (lt_trans zero_lt_one hZ) (ne_of_gt hZ) hT

lemma lowCentralShift_bound (Z T ell ε : ℝ) (hZ : 1<Z) (hT : 0<T) (hε : 0≤ε)
    (hlo : Z^(1+ell-ε/2)≤T) (hhi : T≤Z^(1+ell+ε/2)) :
    |lowCentralShift Z T (ell+ε/2)|≤ε := by
  have he := lowCentralShift_scale Z T (ell+ε/2) hZ hT
  rw [←he,Real.rpow_le_rpow_left_iff hZ] at hlo hhi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma lowCentral_ratio_bounds (Z T ell ε : ℝ) (hZ : 0<Z)
    (hlo : Z^(-ε/2)≤T/Z^(1+ell)) (hhi : T/Z^(1+ell)≤Z^(ε/2)) :
    Z^(1+ell-ε/2)≤T ∧ T≤Z^(1+ell+ε/2) := by
  constructor
  · have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hZ (1+ell))).mp hlo
    convert hh using 1
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  · have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hZ (1+ell))).mp hhi
    convert hh using 1
    rw [←Real.rpow_add hZ]
    congr 1
    ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1778

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowNominalEnergy.lean; sha256: f3ebfbc28c9d50e097c63c44214fda22391890846cb42d614d9e62420955d6e0 -/
section Source1779
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem low_selected_nominal_energy (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (Ck b ε : ℝ) (hCk : 0<Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(R : Finset O),
      (∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^(5/6-2*lowUnselectedLength ell J))→
    ∀X : ℝ,0<X→Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^((5/6-2*lowUnselectedLength ell J)+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_selected_physical_energy η S hS hbad K Ck ε hCk hε hε1
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [eventually_low_selected_caps ell hell b ε hε,Filter.eventually_ge_atTop Z₀] with Z hc hZ
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J R hR X hX hXlo hXhi W hW Y t σ
  obtain ⟨hd,hd1,hs,hscap⟩ := lowLength_bounds ell hell hsum J
  have hscale := lowCentralShift_scale Z X (lowSelectedLength ell J+ε/2) hc.1 hX
  rw [←hscale]
  apply he Z (lowUnselectedLength ell J) (lowSelectedLength ell J+ε/2)
    (lowCentralShift Z X (lowSelectedLength ell J+ε/2)) hZ hd hd1 (by linarith) (by linarith)
    (lowCentralShift_bound Z X (lowSelectedLength ell J) ε hc.1 hX hε.le hXlo hXhi)
    R hR T hT hout hdis J (fun i=>max 1 (b*Z^(ell i.val)))
    (fun i=>le_max_left _ _)
    (fun i P hP=>(hnorm i.val P hP).trans (le_max_right _ _)) (hc.2 J) W hW Y t σ

end SevenEighths.ProbePhysical
end

end OAI

end Source1779

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowInverseNormalize.lean; sha256: 384124deace73ecac59856f5d39090e5df9aed167825adf29728f68e83152648 -/
section Source1780
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma low_inverse_power_cancel (Z d α : ℝ) (hZ : 0<Z) :
    Z^(5/6-2*d+α)*(Z^d)^2/Z^(5/6:ℝ)=Z^α := by
  have hp : (Z^d)^2=Z^(2*d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  rw [hp,←Real.rpow_add hZ,←Real.rpow_sub hZ]
  congr 1
  ring

lemma low_inverse_sqrt_normalized (q C B Z L d α H E : ℝ) (n : ℕ)
    (hq : 0<q) (hC : 0≤C) (_hB : 0≤B) (hZ : 0<Z) (hL : 0<L) (hH : 1≤H)
    (hE : 0≤E) (hEL : E≤C*H^n*Z^(5/6-2*d+α)) (hLB : L≤B*Z^d) :
    Real.sqrt E/Real.sqrt (q*Z^(5/6:ℝ)/L^2)≤
      Real.sqrt (C*B^2/q)*H^n*Z^(α/2) := by
  have hratio : E/(q*Z^(5/6:ℝ)/L^2)≤(C*B^2/q)*H^n*Z^α := by
    calc
      _≤(C*H^n*Z^(5/6-2*d+α))/(q*Z^(5/6:ℝ)/L^2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _=(C*H^n*Z^(5/6-2*d+α))*L^2/(q*Z^(5/6:ℝ)) := by field_simp
      _≤(C*H^n*Z^(5/6-2*d+α))*(B*Z^d)^2/(q*Z^(5/6:ℝ)) := by
        gcongr
      _=(C*B^2/q)*H^n*(Z^(5/6-2*d+α)*(Z^d)^2/Z^(5/6:ℝ)) := by ring
      _=_ := by rw [low_inverse_power_cancel Z d α hZ]
  rw [←Real.sqrt_div hE]
  apply (Real.sqrt_le_sqrt hratio).trans
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
  have hp : Real.sqrt (Z^α)=Z^(α/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
    congr 1
    ring
  rw [hp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hH))) (by positivity)) (by positivity)

end SevenEighths.ProbePhysical
end

end OAI

end Source1780

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowPhysicalInverseBound.lean; sha256: 9991e2ce061afdfdeb0e12439364f38ac1bc3a734fcaa0b19905674563f14797 -/
section Source1781
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem low_physical_inverse_normalized (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b aCut bCut ε : ℝ) (ha : 0<a) (haCut : 0<aCut) (hbCut : 0<bCut)
    (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J),
    ∀X : ℝ,0<X→Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
      ∀(hX0 : 0<Z^(17/48:ℝ)/L)(hY0 : 0<Z^(23/48:ℝ)/L),
      (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) aCut bCut haCut hbCut
          (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) hX0 hY0
          (lowSelectedInverseRow Finset.univ
            (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W (fun i=>Z^(ell i)) t)
            η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t)≤
        C*(1+‖t‖)^degree*Z^(507*ε/2) := by
  let q := elementNorm (calibrationForSet S hS).generator
  let c := (min 1 a)^K
  let B := (max 1 b)^K
  have hq : 0<q := calibration_elementNorm_pos _
  have hc : 0<c := by dsimp [c];positivity
  have hB : 0<B := by dsimp [B];positivity
  let Ck := 2*bCut*(q/c^2)
  have hCk : 0<Ck := by dsimp [Ck];positivity
  obtain ⟨degree,C,ZC,hbound⟩ := low_selected_nominal_energy η S hS hbad ell hell hsum Ck b ε hCk hε hε1
  let C0 := ((Fintype.card RayRing:ℝ)+1)*Real.sqrt (C*B^2/q)/(2*Real.pi)
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
  dsimp only
  let L := elementNorm (∏i : J,(p i).val)
  let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
  intro hX0 hY0
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hL : 0<L := lowUnselectedProduct_norm_pos _
    (fun i n hn=>canonicalSlotSupport_nonzero _ (hT i) n hn) J p
  have hnormE (i : Fin K) (n : O) (hn : n∈canonicalSlotSupport (T i)) :
      a*Z^(ell i)≤elementNorm n ∧ elementNorm n≤b*Z^(ell i) := by
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hLlo : c*Z^(lowUnselectedLength ell J)≤L :=
    lowUnselectedProduct_norm_lower ell a Z ha hz _ (fun i n hn=>(hnormE i n hn).1) J p
  have hLhi : L≤B*Z^(lowUnselectedLength ell J) :=
    lowUnselectedProduct_norm_upper_nominal ell b Z hz _ (fun i n hn=>(hnormE i n hn).2) J p
  have hQ : 0<Q := lowPhysicalScale_pos _ _ _ hX0 hY0
  let R := lowNumeratorRows aCut bCut haCut hbCut Q hQ
  let row := lowSelectedInverseRow Finset.univ
    (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W (fun i=>Z^(ell i)) t)
    η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t
  have hrows : ∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^(5/6-2*lowUnselectedLength ell J) := by
    intro z hzR
    refine ⟨lowNumeratorRows_nonzero aCut bCut haCut hbCut Q hQ z hzR,?_⟩
    apply (lowNumeratorRows_norm_bound aCut bCut haCut hbCut Q hQ z hzR).trans
    have hh := mul_le_mul_of_nonneg_left
      (lowPhysicalScale_nominal_bound (calibrationForSet S hS) Z L c (lowUnselectedLength ell J) hz hc hLlo)
      (show 0≤2*bCut by positivity)
    simpa only [Ck,mul_assoc] using hh
  have he (σ : RayRing) : (∑z∈R,‖row σ z‖^2)≤
      C*(1+‖t‖)^degree*Z^(5/6-2*lowUnselectedLength ell J+507*ε) :=
    hZ.2 T hT hout hdis (fun i P hP=>(hnorm i P hP).2) J R hrows X hX hXlo hXhi W hW (fun i=>Z^(ell i)) t σ
  have hn (σ : RayRing) : Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q≤
      Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^(507*ε/2) := by
    dsimp only [Q]
    rw [lowPhysicalScale_source _ Z L hz]
    exact low_inverse_sqrt_normalized q C B Z L (lowUnselectedLength ell J) (507*ε) (1+‖t‖)
      (∑z∈R,‖row σ z‖^2) degree hq ZC.le hB.le hz hL (le_add_of_nonneg_right (norm_nonneg t))
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _)) (he σ) hLhi
  change (Real.sqrt Q)⁻¹/(2*Real.pi)*(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2))≤_
  calc
    _=(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q)/(2*Real.pi) := by
      rw [←Finset.sum_div]
      ring
    _≤(∑σ : RayRing,Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^(507*ε/2))/(2*Real.pi) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun σ _=>hn σ)) (by positivity)
    _≤_ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp [C0]
      calc
        _=((Fintype.card RayRing:ℝ)*Real.sqrt (C*B^2/q)/(2*Real.pi))*(1+|t|)^degree*Z^(507*ε/2) := by ring
        _≤_ := by gcongr ; linarith

end SevenEighths.ProbePhysical
end

end OAI

end Source1781

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowUnselectedMass.lean; sha256: f990fd7ad91c20736be9c1a43719301b46b7cf3ed3efff33950b4c833327a879 -/
section Source1782
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

lemma canonical_slot_inverse_square : ∃C : ℝ,0<C ∧
    ∀(T : Finset PrimeIdeal)(_hT : ∀P∈T,Supported P.val),
      (∑a : canonicalSlotSupport T,elementNorm a.val^(-2:ℝ))≤C := by
  obtain ⟨C,hC,hb⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-2) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro T hT
  let f : T→SupportedIdeal := fun P=>⟨P.val.val,hT P.val P.property⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : SupportedIdeal=>I.val) h
  have he : (∑a : canonicalSlotSupport T,elementNorm a.val^(-2:ℝ))=
      ∑I∈Finset.univ.image f,ProbeGramCommon.gramIdealNorm I^(-2:ℝ) := by
    rw [Finset.sum_image (fun P _ Q _ h=>hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp (fun a=>elementNorm a.val^(-2:ℝ))
    rw [←hh]
    apply Finset.sum_congr rfl
    intro P hP
    rw [canonicalSlotEquiv_norm]
    rfl
  rw [he]
  exact hb _

lemma lowUnselectedWeight_norm_identity {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (a : LowUnselectedTuple slots J) :
    ‖lowUnselectedWeight slots J W P a‖*elementNorm (∏i : J,(a i).val)^(-(1/2:ℝ))=
      ∏i : J,elementNorm (a i).val^(-2:ℝ)*‖W i.val (elementNorm (a i).val/P i.val)‖ := by
  have hL := lowUnselectedProduct_norm_pos slots hslots J a
  rw [lowUnselectedWeight,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL.le _),norm_prod]
  calc
    _=(elementNorm (∏i : J,(a i).val)^(-(3/2:ℝ))*elementNorm (∏i : J,(a i).val)^(-(1/2:ℝ)))*
        ∏i : J,‖W i.val (elementNorm (a i).val/P i.val)‖ := by ring
    _=elementNorm (∏i : J,(a i).val)^(-2:ℝ)*∏i : J,‖W i.val (elementNorm (a i).val/P i.val)‖ := by
      rw [←Real.rpow_add hL]
      norm_num
    _=_ := by
      rw [elementNorm_finset_prod,Finset.prod_mul_distrib,Real.finsetProd_rpow Finset.univ
        (fun i : J=>elementNorm (a i).val) (fun i _=>by unfold elementNorm;positivity)]

theorem lowUnselectedMass_bound (K : ℕ) (M : ℝ) (hM : 0≤M) :
    ∃C : ℝ,0<C ∧ ∀(T : Fin K→Finset PrimeIdeal)(_hT : ∀i P,P∈T i→Supported P.val)
      (J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
      (∀i x,‖W i x‖≤M)→
      (∑a : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W P a‖*
          elementNorm (∏i : J,(a i).val)^(-(1/2:ℝ)))≤C := by
  obtain ⟨C,hC,hb⟩ := canonical_slot_inverse_square
  refine ⟨(max 1 (C*M))^K,by positivity,?_⟩
  intro T hT J W P hW
  simp_rw [lowUnselectedWeight_norm_identity _ (fun i=>canonicalSlotSupport_nonzero _ (hT i))]
  rw [←Fintype.prod_sum (fun (i : J) (a : canonicalSlotSupport (T i.val))=>
    elementNorm a.val^(-2:ℝ)*‖W i.val (elementNorm a.val/P i.val)‖)]
  calc
    _≤∏i : J,C*M := by
      apply Finset.prod_le_prod₀ (fun i _=>Finset.sum_nonneg (fun a _=>mul_nonneg (Real.rpow_nonneg (by unfold elementNorm;positivity) _) (norm_nonneg _)))
      intro i hi
      calc
        _≤∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-2:ℝ)*M := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hW i.val _) (Real.rpow_nonneg (by unfold elementNorm;positivity) _)
        _=(∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-2:ℝ))*M := (Finset.sum_mul ..).symm
        _≤C*M := mul_le_mul_of_nonneg_right (hb _ (hT i.val)) hM
    _≤∏_i : J,max 1 (C*M) := Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun _ _=>le_max_right _ _)
    _≤_ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe]
      exact pow_le_pow_right₀ (le_max_left _ _) (by simpa using Finset.card_le_card (Finset.subset_univ J))

end SevenEighths.ProbePhysical
end

end OAI

end Source1782

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowCentralTuple.lean; sha256: 874b63c1d6d28a956d7448a1a14d9ebbef2835c98fe43840f0cc7a895cae610c -/
section Source1783
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_compensated_sqrt_factor (q L : ℝ) (hq : 0≤q) (hL : 0<L) :
    Real.sqrt (3*q/L)=Real.sqrt (3*q)*L^(-(1/2:ℝ)) := by
  rw [Real.sqrt_div (by positivity)]
  simp only [div_eq_mul_inv,Real.sqrt_eq_rpow,Real.rpow_neg hL.le]

theorem low_central_compensated_tuple (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(X : ℝ),0<X→
      Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      ‖∑p : ∀i,canonicalSlotSupport (T i),
        compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J*
          compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J
            (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) X t*
          selectedSlotFactor W (fun i=>Z^(ell i)) (fun i=>(p i).val) J t‖≤
        C*(1+‖t‖)^degree*Z^(3/16+254*ε) := by
  obtain ⟨Cg,hCg,hgram⟩ := compensation_tuple_actual_gram ε hε hε1 W0 W1
    a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM S hS hbad
  obtain ⟨degree,Ci,hCi,hinverse⟩ := low_physical_inverse_normalized η S hS hbad ell hell hsum
    a b (a0*a1) (max 1 (b0*b1)) ε ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1.le
  obtain ⟨Cu,hCu,hmass⟩ := lowUnselectedMass_bound K 1 (by norm_num)
  let q := elementNorm (calibrationForSet S hS).generator
  have hq : 0<q := calibration_elementNorm_pos _
  let C0 := Cg*Ci*Real.sqrt (3*q)*Cu
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hinverse,eventually_original_slot_scales (calibrationForSet S hS)
    ell hell hsum (max 1 b) (le_max_left _ _)] with Z hInv hScale
  refine ⟨hInv.1,?_⟩
  intro T hT hout hdis hnorm J X hX hXlo hXhi W hW t
  let slots := fun i=>canonicalSlotSupport (T i)
  let Yp := fun i=>Z^(ell i)
  have hz : 0<Z := lt_trans zero_lt_one hInv.1
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈slots i→elementNorm n≤max 1 b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := hScale.2 slots hslots hnormE J
  have hg := hgram K η slots hslots J W Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) X t
    (by positivity) (by positivity) hX (fun p=>(hs p).1) (fun p=>(hs p).2.1)
  apply hg.trans
  let G := Z^(3/16+(23/96)*ε:ℝ)
  let V := Ci*(1+‖t‖)^degree*Z^(507*ε/2)
  have hGV : G*V≤Ci*(1+‖t‖)^degree*Z^(3/16+254*ε) := by
    dsimp only [G,V]
    calc
      _=Ci*(1+‖t‖)^degree*(Z^(3/16+(23/96)*ε:ℝ)*Z^(507*ε/2)) := by ring
      _≤_ := by
        rw [←Real.rpow_add hz]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hInv.1.le (by linarith)
  have hterm (p : LowUnselectedTuple slots J) :
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
      ‖lowUnselectedWeight slots J W Yp p‖*((Real.sqrt Q)⁻¹/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ε*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
            η S hS (lowSelectedIdeal slots J) X t)≤
      (Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(3/16+254*ε))*
        (‖lowUnselectedWeight slots J W Yp p‖*L^(-(1/2:ℝ))) := by
    dsimp only
    let L := elementNorm (∏i : J,(p i).val)
    let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
    have hL := lowUnselectedProduct_norm_pos slots hslots J p
    have hgb := (hs p).2.2 ε hε.le
    have hib := hInv.2 T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
      (div_pos (by positivity) hL) (div_pos (by positivity) hL)
    have hgn : 0≤lowGramFactor (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ε := Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_left hib
      (mul_nonneg (norm_nonneg (lowUnselectedWeight slots J W Yp p)) hgn)
    have hh2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgb (norm_nonneg (lowUnselectedWeight slots J W Yp p)))
      (show 0≤V by dsimp [V];positivity)
    calc
      _=‖lowUnselectedWeight slots J W Yp p‖*
        lowGramFactor (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ε*
        (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
          (div_pos (by positivity) hL) (div_pos (by positivity) hL)
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t) η S hS (lowSelectedIdeal slots J) X t) := by ring
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*(G*V) := by
        have hh3 := hh.trans hh2
        simp only [G,V,div_eq_mul_inv,mul_assoc] at hh3 ⊢
        convert hh3 using 1 ; congr 7
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*
          (Ci*(1+‖t‖)^degree*Z^(3/16+254*ε)) :=
        mul_le_mul_of_nonneg_left hGV (by positivity)
      _=_ := by rw [low_compensated_sqrt_factor q L hq.le hL];ring
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hterm p)) hCg.le
  apply hh.trans
  rw [←Finset.mul_sum]
  have hm := hmass T hT J W Yp hW
  calc
    _≤Cg*((Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(3/16+254*ε))*Cu) := by gcongr
    _=_ := by dsimp [C0];ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1783

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianCrude.lean; sha256: c8ea9217ae1dce3d0b1900b7fedea2def02235c209737da880ffc8ff61e1aa59 -/
section Source1784
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CubicEisenstein FourierBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gaussianAnnulus_norm_le_one (y : ℝ) : ‖gaussianAnnulus y‖≤1 := by
  rw [gaussianAnnulus_norm]
  change Real.smoothTransition (2-y)-Real.smoothTransition (2-2*y)≤1
  linarith [Real.smoothTransition.le_one (2-y),Real.smoothTransition.nonneg (2-2*y)]

lemma gaussianAnnulus_scaled_square (N T : ℝ) (hN : 0<N) (hT : 0<T) :
    N^2*‖gaussianAnnulus (N/T)‖≤4*T^2 := by
  by_cases hz : gaussianAnnulus (N/T)=0
  · rw [hz,norm_zero,mul_zero]
    positivity
  have hn : N/T<2 := by
    by_contra hh
    exact hz (gaussianAnnulus_large _ (le_of_not_gt hh))
  have hn' : N<2*T := (div_lt_iff₀ hT).mp hn
  calc
    _ ≤ N^2 := mul_le_of_le_one_right (sq_nonneg _) (gaussianAnnulus_norm_le_one _)
    _ ≤ _ := by nlinarith

lemma gaussianFixedWindow_spectral_identity (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (T t : ℝ) (hT : 0<T) (I J : Id) (hI : I≠0) (hJ : J≠0) :
    correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T I J=
      spectralSummand S D Ψ 2 I J*
        ((((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3:ℝ):ℂ)^2*
          (gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T)*
            logPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T)))) := by
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hic : (Ideal.absNorm I:ℂ)≠0 := by exact_mod_cast hi.ne'
  have hjc : (Ideal.absNorm J:ℂ)≠0 := by exact_mod_cast hj.ne'
  unfold correctedSummand markedSummand CompletedGauss.summand spectralSummand fullIdealWeight
  rw [gaussianFixedWindow_Vstar_twist t _ (div_pos (mul_pos hi (pow_pos hj 3)) hT)]
  simp only [ite_eq_right hI,ite_eq_right hJ]
  norm_num only [show (3:ℂ)*2=6 by norm_num,Complex.cpow_neg,Complex.cpow_ofNat]
  push_cast
  field_simp

lemma gaussianFixedWindow_summand_crude (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (T t : ℝ) (hT : 0<T) (I J : Id) :
    ‖correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T I J‖≤
      4*T^2*rowMajorant 2 (I,J) := by
  by_cases hI : I=0
  · subst I
    simp only [correctedSummand,markedSummand,summand_zero_left,mul_zero,norm_zero]
    unfold rowMajorant
    positivity
  by_cases hJ : J=0
  · subst J
    simp only [correctedSummand,markedSummand,summand_zero_right,mul_zero,norm_zero]
    unfold rowMajorant
    positivity
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hN : 0<(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := mul_pos hi (pow_pos hj 3)
  rw [gaussianFixedWindow_spectral_identity S D Ψ T t hT I J hI hJ,
    norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN,
    norm_mul,logPhase_norm,mul_one]
  have hs : ‖spectralSummand S D Ψ 2 I J‖≤rowMajorant 2 (I,J) := by
    simpa only [Complex.ofReal_ofNat,Complex.ofReal_zero,zero_mul,add_zero] using
      spectralSummand_vertical_bound S D Ψ hΨ 2 0 (I,J)
  have hn := gaussianAnnulus_scaled_square _ T hN hT
  exact (mul_le_mul hs hn (by positivity) (by unfold rowMajorant;positivity)).trans_eq (by ring)

theorem gaussianFixedWindow_completed_crude :
    ∃C : ℝ,0<C ∧ ∀S : Finset Id,∀D : Id,∀Ψ : O→*ℂ,
      (∀n,‖Ψ n‖≤1)→∀T t : ℝ,0<T→
      ‖correctedCompletedT S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T‖≤C*T^2 := by
  let M : ℝ := ∑'p : Id×Id,rowMajorant 2 p
  have hM : 0≤M := tsum_nonneg (fun p=>by unfold rowMajorant;positivity)
  refine ⟨4*M+1,by positivity,?_⟩
  intro S D Ψ hΨ T t hT
  have hs := correctedSummand_summable S D Ψ _ (gaussianFixedWindow_twist_compact t) T hT
  change ‖∑'p : Id×Id,correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2‖≤_
  calc
    _ ≤ ∑'p : Id×Id,‖correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑'p : Id×Id,4*T^2*rowMajorant 2 p := hs.norm.tsum_le_tsum
      (fun p=>gaussianFixedWindow_summand_crude S D Ψ hΨ T t hT p.1 p.2)
      ((rowMajorant_summable 2 (by norm_num)).mul_left (4*T^2))
    _ = (4*M)*T^2 := by rw [tsum_mul_left];dsimp only [M];ring
    _ ≤ _ := by nlinarith [sq_nonneg T]

end SevenEighths.ProbePhysical
end

end OAI

end Source1784

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianTailBudget.lean; sha256: 38f614d4aa36aff2966a4143f0fd73876902f38004d643acf22d3a41716f071b -/
section Source1785
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianWeightedMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k R : ℝ) : ℝ := R^k*gaussianJointMoment V hV J R

lemma gaussianWeightedMoment_nonneg (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k R : ℝ) (hR : 0≤R) : 0≤gaussianWeightedMoment V hV J k R := by
  unfold gaussianWeightedMoment
  exact mul_nonneg (Real.rpow_nonneg hR _) (gaussianJointMoment_nonneg V hV J R)

lemma gaussianWeightedMoment_power_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k A : ℝ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→gaussianWeightedMoment V hV J k R≤C*R^(-A) := by
  obtain ⟨C,hC,hb⟩ := gaussianJointMoment_power_bound V hV J (A+k)
  refine ⟨C,hC,?_⟩
  intro R hR
  have hh := mul_le_mul_of_nonneg_left (hb R hR) (Real.rpow_nonneg hR.le k)
  change R^k*gaussianJointMoment V hV J R≤_
  calc
    _ ≤ R^k*(C*R^(-(A+k))) := hh
    _ = C*R^(-A) := by
      rw [←mul_assoc,mul_comm (R^k) C,mul_assoc,←Real.rpow_add hR]
      congr 2
      ring

lemma gaussianWeightedMoment_polynomial_decay (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (k : ℝ) (N : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→gaussianWeightedMoment V hV J k R≤C/(1+R)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianWeightedMoment_power_bound V hV J k 0
  obtain ⟨C,hC,hdecay⟩ := gaussianWeightedMoment_power_bound V hV J k (N:ℝ)
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

theorem gaussianWeightedMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (k s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,0<Z→
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z))≤C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianWeightedMoment_polynomial_decay V hV J k N
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound ((2:ℝ)^j/Z) (div_pos (by positivity) hZ))
      (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z) :=
    mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s) (gaussianWeightedMoment_nonneg V hV J k _ (by positivity))
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

def gaussianRemoteMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (s Z A : ℝ) (j : ℕ) : ℝ :=
  if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
    ((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)
  else 0

theorem gaussianRemoteMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J N : ℕ) (s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀Z A : ℝ,0<Z→1≤A→
      Summable (gaussianRemoteMoment V hV J s Z A) ∧
      (∑'j : ℕ,gaussianRemoteMoment V hV J s Z A j)≤C*Z^s/A^N := by
  obtain ⟨Cm,hCm,hm⟩ := gaussianWeightedMoment_summed V hV J (-(N:ℝ)) s hs
  obtain ⟨Cp,hCp,hp⟩ := gaussianWeightedMoment_summed V hV J (N:ℝ) s hs
  refine ⟨Cm+Cp,by positivity,?_⟩
  intro Z A hZ hA
  have hAp : 0<A := lt_of_lt_of_le zero_lt_one hA
  have hAN : 0<A^N := pow_pos hAp N
  obtain ⟨hsm,htm⟩ := hm Z hZ
  obtain ⟨hsp,htp⟩ := hp Z hZ
  let U : ℕ→ℝ := fun j=>
    (((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (-(N:ℝ)) ((2:ℝ)^j/Z)+
      ((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (N:ℝ) ((2:ℝ)^j/Z))/A^N
  have hU : Summable U := (hsm.add hsp).div_const _
  have hnon (j : ℕ) : 0≤gaussianRemoteMoment V hV J s Z A j := by
    unfold gaussianRemoteMoment
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianJointMoment_nonneg V hV J _)
    · rfl
  have hb (j : ℕ) : gaussianRemoteMoment V hV J s Z A j≤U j := by
    let R := (2:ℝ)^j/Z
    have hR : 0<R := div_pos (by positivity) hZ
    have hM : 0≤gaussianJointMoment V hV J R := gaussianJointMoment_nonneg V hV J R
    unfold gaussianRemoteMoment
    split_ifs with hj
    · have he : A^N≤R^(-(N:ℝ))+R^(N:ℝ) := by
        rcases hj with hlo|hhi
        · have hra : R*A≤1 := (le_div_iff₀ hAp).mp (by simpa only [one_div,R] using hlo)
          have hh := pow_le_pow_left₀ (by positivity : 0≤R*A) hra N
          rw [mul_pow,one_pow] at hh
          have hi : A^N≤R^(-(N:ℝ)) := by
            rw [Real.rpow_neg hR.le,Real.rpow_natCast]
            rw [←one_div]
            exact (le_div_iff₀ (pow_pos hR N)).mpr (by simpa only [mul_comm] using hh)
          exact hi.trans (le_add_of_nonneg_right (Real.rpow_nonneg hR.le _))
        · have hi : A^N≤R^(N:ℝ) := by
            rw [Real.rpow_natCast]
            exact pow_le_pow_left₀ hAp.le hhi N
          exact hi.trans (le_add_of_nonneg_left (Real.rpow_nonneg hR.le _))
      change ((2:ℝ)^j)^s*gaussianJointMoment V hV J R≤_
      dsimp only [U]
      apply (le_div_iff₀ hAN).mpr
      calc
        _ ≤ (((2:ℝ)^j)^s*gaussianJointMoment V hV J R)*(R^(-(N:ℝ))+R^(N:ℝ)) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg (by positivity) _) hM)
        _ = _ := by unfold gaussianWeightedMoment;dsimp only [R];ring
    · dsimp only [U]
      apply div_nonneg _ hAN.le
      exact add_nonneg
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianWeightedMoment_nonneg V hV J _ _ hR.le))
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianWeightedMoment_nonneg V hV J _ _ hR.le))
  have hsum := Summable.of_nonneg_of_le hnon hb hU
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,U j := hsum.tsum_le_tsum hb hU
    _ = ((∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (-(N:ℝ)) ((2:ℝ)^j/Z))+
        (∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (N:ℝ) ((2:ℝ)^j/Z)))/A^N := by
      dsimp only [U]
      rw [tsum_div_const,hsm.tsum_add hsp]
    _ ≤ (Cm*Z^s+Cp*Z^s)/A^N := div_le_div_of_nonneg_right (add_le_add htm htp) hAN.le
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1785

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianRemoteRows.lean; sha256: 322034af461135599f4966ed12fbf265b0d20babfc24582a2fa3071095767dc6 -/
section Source1786
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss FourierBridge
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianCompletedFamilyIntegral {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) : ℂ :=
  ∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
    (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
    (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t

def gaussianCompletedFamilyMass {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*∏i,‖W i (q k i)‖

lemma gaussianCompletedFamilyMass_nonneg {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (W : ι→ℝ→ℂ) (q : α→ι→ℝ) :
    0≤gaussianCompletedFamilyMass F a W q := by
  unfold gaussianCompletedFamilyMass
  positivity

lemma gaussianCompletedFamily_integrable {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) (hT : 0<T) :
    Integrable (fun t : ℝ=>(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
      (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t) := by
  have hh := integrable_finsetSum F (fun k _=>(gaussian_selected_completed_integrable W (q k)
    (gaussianJointDensity V hV (T/Z)) S (D k) (Ψ k) T hT).const_mul (a k))
  simpa only [Finset.sum_mul,mul_assoc] using hh

theorem gaussianCompletedFamily_crude :
    ∃C : ℝ,0<C ∧ ∀{α ι : Type*} [Fintype ι],∀F : Finset α,∀a : α→ℂ,
      ∀S : Finset Id,∀D : α→Id,∀Ψ : α→O→*ℂ,
      (∀k∈F,∀n,‖Ψ k n‖≤1)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀V : SchwartzMap ℝ ℂ,∀hV : HasCompactSupport (V:ℝ→ℂ),∀T Z : ℝ,0<T→
      ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV T Z‖≤
        C*T^2*gaussianCompletedFamilyMass F a W q*gaussianJointMoment V hV 0 (T/Z) := by
  obtain ⟨C,hC,hb⟩ := gaussianFixedWindow_completed_crude
  refine ⟨C,hC,?_⟩
  intro α ι _ F a S D Ψ hΨ W q V hV T Z hT
  have hf := gaussianCompletedFamily_integrable F a S D Ψ W q V hV T Z hT
  have hp (t : ℝ) :
      ‖(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t‖≤
      (C*T^2*gaussianCompletedFamilyMass F a W q)*‖gaussianJointDensity V hV (T/Z) t‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ∑k∈F,‖a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i)))‖ := norm_sum_le _ _
      _ ≤ ∑k∈F,‖a k‖*(C*T^2)*(∏i,‖W i (q k i)‖) := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [norm_mul,norm_prod,logPhase_norm,mul_one]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hb S (D k) (Ψ k) (hΨ k hk) T t hT) (norm_nonneg _))
          (Finset.prod_nonneg (fun _ _=>norm_nonneg _))
      _ = _ := by unfold gaussianCompletedFamilyMass;rw [Finset.mul_sum];congr 1;funext k;ring
  calc
    _ ≤ ∫t : ℝ,‖(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫t : ℝ,(C*T^2*gaussianCompletedFamilyMass F a W q)*‖gaussianJointDensity V hV (T/Z) t‖ :=
      integral_mono hf.norm ((gaussianJointDensity V hV (T/Z)).integrable.norm.const_mul _) hp
    _ = _ := by simp only [integral_const_mul,gaussianJointMoment,pow_zero,one_mul]

theorem gaussianCompletedFamily_remote (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ) :
    ∃C : ℝ,0<C ∧ ∀{α ι : Type*} [Fintype ι],∀F : Finset α,∀a : α→ℂ,
      ∀S : Finset Id,∀D : α→Id,∀Ψ : α→O→*ℂ,
      (∀k∈F,∀n,‖Ψ k n‖≤1)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0<Z→1≤A→
      Summable (fun j : ℕ=>if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          C*gaussianCompletedFamilyMass F a W q*Z^2/A^N := by
  obtain ⟨Cr,hCr,hr⟩ := gaussianCompletedFamily_crude
  obtain ⟨Cg,hCg,hg⟩ := gaussianRemoteMoment_summed V hV 0 N 2 (by norm_num)
  refine ⟨Cr*Cg,by positivity,?_⟩
  intro α ι _ F a S D Ψ hΨ W q Z A hZ hA
  obtain ⟨hs,ht⟩ := hg Z A hZ hA
  let M := gaussianCompletedFamilyMass F a W q
  have hM : 0≤M := gaussianCompletedFamilyMass_nonneg F a W q
  have hb (j : ℕ) :
      (if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0)≤
      (Cr*M)*gaussianRemoteMoment V hV 0 2 Z A j := by
    unfold gaussianRemoteMoment
    split_ifs
    · simpa only [M,Real.rpow_two,mul_assoc,mul_comm,mul_left_comm] using
        hr F a S D Ψ hΨ W q V hV ((2:ℝ)^j) Z (by positivity)
    · simp
  have hnon (j : ℕ) : 0≤(if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
      ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0) := by split_ifs <;> positivity
  have hsum := Summable.of_nonneg_of_le hnon hb (hs.mul_left (Cr*M))
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,(Cr*M)*gaussianRemoteMoment V hV 0 2 Z A j := hsum.tsum_le_tsum hb (hs.mul_left (Cr*M))
    _ = (Cr*M)*∑'j : ℕ,gaussianRemoteMoment V hV 0 2 Z A j := tsum_mul_left
    _ ≤ (Cr*M)*(Cg*Z^(2:ℝ)/A^N) := mul_le_mul_of_nonneg_left ht (mul_nonneg hCr.le hM)
    _ = _ := by rw [Real.rpow_two];dsimp only [M];ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1786

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianPhysicalTail.lean; sha256: c0c2845cc3dd4fe5e30ffdb06c43a73adde64a170386060bcac5b51465095a32 -/
section Source1787
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss FourierBridge
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianPhysicalFamilyIntegral {α ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (F : Finset α) (a : α→ℂ) (D : α→Id) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) : ℂ :=
  ∫t : ℝ,(∑k∈F,a k*
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
      correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T)*
    (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t

def gaussianPhysicalFamilyMass {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*(∏i,‖W i (q k i)‖)*∑'r : PhysicalRowIndex,‖physicalRowWeight C W0 W1 (X k) (Y k) r‖

lemma gaussianPhysicalFamily_mass_eq {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (R : Finset PhysicalRowIndex)
    (hR : ∀k∈F,∀r∉R,physicalRowWeight C W0 W1 (X k) (Y k) r=0) :
    gaussianCompletedFamilyMass (F×ˢR)
      (fun p=>a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2) W (fun p=>q p.1)=
      gaussianPhysicalFamilyMass C W0 W1 F a X Y W q := by
  unfold gaussianCompletedFamilyMass gaussianPhysicalFamilyMass
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  rw [tsum_eq_sum (s:=R) (fun r hr=>by rw [hR k hk r hr,norm_zero]),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [norm_mul]
  ring

lemma gaussianPhysicalFamily_integral_eq {α ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (F : Finset α) (a : α→ℂ) (D : α→Id) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) (R : Finset PhysicalRowIndex)
    (hR : ∀k∈F,∀r∉R,physicalRowWeight C W0 W1 (X k) (Y k) r=0) :
    gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV T Z=
      gaussianCompletedFamilyIntegral (F×ˢR)
        (fun p=>a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2)
        C.excluded (fun p=>D p.1) (fun p=>physicalRowMonoid η C p.2) W (fun p=>q p.1) V hV T Z := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  rw [tsum_eq_sum (s:=R) (fun r hr=>by rw [hR k hk r hr,zero_mul]),Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem gaussianPhysicalFamily_remote (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ) :
    ∃C0 : ℝ,0<C0 ∧ ∀{α ι : Type*} [Fintype ι],
      ∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
      HasCompactSupport W0→HasCompactSupport W1→
      ∀F : Finset α,∀a : α→ℂ,∀D : α→Id,∀X Y : α→ℝ,
      (∀k∈F,0<X k)→(∀k∈F,0<Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0<Z→1≤A→
      Summable (fun j : ℕ=>if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          C0*gaussianPhysicalFamilyMass C W0 W1 F a X Y W q*Z^2/A^N := by
  obtain ⟨C0,hC0,hb⟩ := gaussianCompletedFamily_remote V hV N
  refine ⟨C0,hC0,?_⟩
  intro α ι _ η C W0 W1 hW0 hW1 F a D X Y hX hY W q Z A hZ hA
  obtain ⟨R,hR⟩ := physicalRows_common_finset C W0 W1 hW0 hW1 F X Y hX hY
  have hh := hb (F×ˢR) (fun p=>a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2)
    C.excluded (fun p=>D p.1) (fun p=>physicalRowMonoid η C p.2)
    (fun p _=>physicalRowMonoid_norm η C p.2) W (fun p=>q p.1) Z A hZ hA
  rw [gaussianPhysicalFamily_mass_eq C W0 W1 F a X Y W q R hR] at hh
  simpa only [gaussianPhysicalFamily_integral_eq η C W0 W1 F a D X Y W q V hV _ Z R hR] using hh

end SevenEighths.ProbePhysical
end

end OAI

end Source1787

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianPhysicalMass.lean; sha256: 2cbd12dbfc4ab2a97160cd8d9733e7867ac7e0c75c9c974fe37be5498d4d0c32 -/
section Source1788
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianPhysicalScaleMass {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*(∏i,‖W i (q k i)‖)*lowPhysicalScale C (X k) (Y k)

theorem gaussianPhysicalFamily_mass_bound (a0 b0 a1 b1 B0 B1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀{α ι : Type*} [Fintype ι],
      ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,∀_hW1c : HasCompactSupport W1,
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀F : Finset α,∀a : α→ℂ,∀X Y : α→ℝ,
      (∀k∈F,1≤X k)→(∀k∈F,1≤Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      gaussianPhysicalFamilyMass (calibrationForSet S hS) W0 W1 F a X Y W q≤
        K*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q := by
  obtain ⟨K,hK,hb⟩ := physicalRowWeight_source_mass a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  refine ⟨K,hK,?_⟩
  intro α ι _ S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 F a X Y hX hY W q
  unfold gaussianPhysicalFamilyMass gaussianPhysicalScaleMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ (‖a k‖*(∏i,‖W i (q k i)‖))*(K*lowPhysicalScale (calibrationForSet S hS) (X k) (Y k)) :=
      mul_le_mul_of_nonneg_left (hb S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 (X k) (Y k) (hX k hk) (hY k hk)) (by positivity)
    _ = _ := by ring

theorem gaussianPhysicalFamily_remote_polynomial (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ)
    (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀{α ι : Type*} [Fintype ι],
      ∀η : HeckeFamily.Character,∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,HasCompactSupport W0→HasCompactSupport W1→
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀F : Finset α,∀a : α→ℂ,∀D : α→Id,∀X Y : α→ℝ,
      (∀k∈F,1≤X k)→(∀k∈F,1≤Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0<Z→1≤A→
      Summable (fun j : ℕ=>if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η (calibrationForSet S hS) W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η (calibrationForSet S hS) W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          K*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q*Z^2/A^N := by
  obtain ⟨C0,hC0,hremote⟩ := gaussianPhysicalFamily_remote V hV N
  obtain ⟨C1,hC1,hmass⟩ := gaussianPhysicalFamily_mass_bound a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  refine ⟨C0*C1,mul_pos hC0 hC1,?_⟩
  intro α ι _ η S hS W0 W1 hW0c hW1c hW0 hW1 hWB0 hWB1 F a D X Y hX hY W q Z A hZ hA
  have hh := hremote η (calibrationForSet S hS) W0 W1 hW0c hW1c F a D X Y
    (fun k hk=>lt_of_lt_of_le zero_lt_one (hX k hk)) (fun k hk=>lt_of_lt_of_le zero_lt_one (hY k hk)) W q Z A hZ hA
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hm := hmass S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 F a X Y hX hY W q
  calc
    _ ≤ C0*(C1*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q)*Z^2/A^N := by gcongr
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1788

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowRemoteMass.lean; sha256: 8b864da5b8e13e548474693eaf72cd29ab0eca3d5bb970bf878613573da64043 -/
section Source1789
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma canonicalSlot_count (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (H : ℝ) (hH : 1≤H) (hnorm : ∀P∈T,(Ideal.absNorm P.val:ℝ)≤H) :
    ((canonicalSlotSupport T).card:ℝ)≤128*H := by
  have hh := DescentFiberCost.finite_ideal_count_real (lowPrimeIdealList T) H hH
    (fun I hI=>(lowPrimeIdealList_prime T I hI).ne_zero) (lowPrimeIdealList_norm T H hnorm)
  have he := Fintype.card_congr (canonicalSlotEquiv T hT)
  simp only [Fintype.card_coe] at he
  rw [lowPrimeIdealList,Finset.card_image_of_injective _ Subtype.val_injective,he] at hh
  exact hh

lemma canonicalTuple_count {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤1/6) (b Z : ℝ) (hZ : 1≤Z)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i)) :
    (Fintype.card (∀i,canonicalSlotSupport (T i)):ℝ)≤(128*max 1 b)^K*Z^(1/6:ℝ) := by
  rw [Fintype.card_pi,Nat.cast_prod]
  calc
    _≤∏i,128*(max 1 b*Z^(ell i)) := by
      apply Finset.prod_le_prod₀ (fun i _=>Nat.cast_nonneg _)
      intro i hi
      simp only [Fintype.card_coe]
      apply canonicalSlot_count _ (hT i) _
        (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i)))
      intro P hP
      exact (hnorm i P hP).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    _=(128*max 1 b)^K*Z^(∑i,ell i) := by
      simp_rw [←mul_assoc]
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
    _≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hsum) (by positivity)

lemma slotProduct_norm_ge_one {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    1≤elementNorm (slotProduct p J) := by
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr (slotProduct_nonzero p hp J)))

lemma compensationSubsetWeight_norm_le_one {K : ℕ} (η : HeckeFamily.Character)
    (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) (Y : Fin K→ℝ)
    (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    ‖compensationSubsetWeight η W Y p J‖≤1 := by
  rw [compensationSubsetWeight,norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) _).trans _
  · rw [compensationSubsetCoefficient,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (slotProduct_norm_pos p hp J).le _),norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos (slotProduct_norm_ge_one p hp J) (by norm_num))).trans (ProbeRow.targetMonoid_norm_le_one η _)
  · rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i _=>hW i _)

lemma compensation_scale_mass_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (b Z : ℝ) (hZ : 1≤Z) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
      (fun p=>compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J)
      (fun p=>Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=>Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=>W i.val)
      (fun p i=>elementNorm (p i.val).val/Z^(ell i.val))≤
        (elementNorm C.generator*(128*max 1 b)^K)*Z := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : ∀i,canonicalSlotSupport (T i)) (i : Fin K) : (p i).val≠0 :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : ∀i,canonicalSlotSupport (T i)) :
      ‖compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)*
        lowPhysicalScale C (Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
          (Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))≤
      elementNorm C.generator*Z^(5/6:ℝ) := by
    have hcoeff : ‖compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)≤1 := (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _=>norm_nonneg _)) (compensationSubsetWeight_norm_le_one η W hW _ _ (hp p) J)).trans (Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun (i : SelectedSlot J) _=>hW i.val _))
    have hL := slotProduct_norm_ge_one _ (hp p) J
    rw [lowPhysicalScale_source C Z _ hz]
    apply (mul_le_of_le_one_left (by unfold elementNorm;positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm;positivity) (one_le_pow₀ hL)
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _=>hterm p)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right (canonicalTuple_count ell hell hsum b Z hZ T hT hnorm)
    (show 0≤elementNorm C.generator*Z^(5/6:ℝ) by unfold elementNorm;positivity)
  apply hc.trans_eq
  calc
    _=(elementNorm C.generator*(128*max 1 b)^K)*(Z^(1/6:ℝ)*Z^(5/6:ℝ)) := by ring
    _=_ := by rw [←Real.rpow_add hz];norm_num

end SevenEighths.ProbePhysical
end

end OAI

end Source1789

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianCommon.lean; sha256: ecacb550c8a12fca88c7df98e7c086808338979f56058cdba850d6fc00ad41a4 -/
section Source1790
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

theorem compensatedPhysicalProbe_common_gaussian {K : ℕ}
    (W : Fin K→ℝ→ℂ) (M : Fin K→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : Finset (Fin K)→SchwartzMap ℝ ℂ,
    ∃hV : ∀A,HasCompactSupport (V A:ℝ→ℂ),
      (∀N : ℕ,∀s : ℝ,0<s→∃B : ℝ,0<B ∧
        ∀A : Finset (Fin K),∀Z : ℝ,0<Z→
          Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z)) ∧
          (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z))≤B*Z^s) ∧
      (∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
        HasCompactSupport W0→HasCompactSupport W1→
        ∀slotPrimes : Fin K→Finset O,(∀i a,a∈slotPrimes i→a≠0)→
        ∀P : Fin K→ℝ,(∀i,0<P i)→∀X Y Z : ℝ,0<X→0<Y→0<Z→
          compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
          ∑A∈(Finset.univ : Finset (Fin K)).powerset,
            ∑'j : ℕ,∫t : ℝ,
              (∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
                compensationSubsetWeight η W P (fun i=>(p i).val) A*
                  compensationRowTest η C W0 W1 (fun i=>(p i).val) A X Y ((2:ℝ)^j) t*
                    selectedSlotFactor W P (fun i=>(p i).val) A t)*
                      gaussianJointDensity (V A) (hV A) ((2:ℝ)^j/(Z*∏i∈Finset.univ\A,P i)) t) := by
  choose V hV hsep hbound using fun A : Finset (Fin K)=>
    gaussian_selected_slot_family (fun i : SelectedSlot A=>W i.val)
      (fun i : SelectedSlot A=>M i.val) (fun i=>hM i.val) (fun i=>hwindow i.val)
  refine ⟨V,hV,?_,?_⟩
  · intro N s hs
    choose B hB hb using fun A : Finset (Fin K)=>gaussianJointMoment_summed (V A) (hV A) N s hs
    let B0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,B A)+1
    have hB0 : 0<B0 := by
      have hh : 0≤∑A∈(Finset.univ : Finset (Fin K)).powerset,B A :=
        Finset.sum_nonneg (fun A _=>(hB A).le)
      dsimp only [B0]
      linarith
    refine ⟨B0,hB0,?_⟩
    intro A Z hZ
    obtain ⟨hsm,hbd⟩ := hb A Z hZ
    refine ⟨hsm,hbd.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le s)
    have hm : A∈(Finset.univ : Finset (Fin K)).powerset := Finset.mem_powerset.mpr (Finset.subset_univ A)
    have hh := Finset.single_le_sum (fun A _=>(hB A).le) hm
    dsimp only [B0]
    linarith
  · intro η C W0 W1 hW0 hW1 slotPrimes hp P hP X Y Z hX hY hZ
    rw [compensatedPhysicalProbe_eq_subsets]
    apply Finset.sum_congr rfl
    intro A hA
    exact compensation_subset_common A W (V A) (hV A) (hsep A) η C W0 W1 hW0 hW1 Finset.univ
      (fun p : ((i : Fin K)→{a : O // a∈slotPrimes i})=>fun i=>(p i).val)
      (fun p _ i=>hp i (p i).val (p i).property) P hP X Y Z hX hY hZ

end SevenEighths.ProbePhysical
end

end OAI

end Source1790

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGaussianDyad.lean; sha256: 75b6ef5ee30a137c9ac18aff9807ca36657f33c8f868fc1e996ff02ffafeaf12 -/
section Source1791
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowCommonDyad {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R : ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) : ℂ :=
  ∫t : ℝ,(∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
    compensationRowTest η C W0 W1 (fun i=>(p i).val) J X Y U t*
      selectedSlotFactor W Yp (fun i=>(p i).val) J t)*gaussianJointDensity V hV (U/R) t

lemma lowCommonDyad_eq_family {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R : ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) :
    lowCommonDyad η C W0 W1 slots W Yp J X Y U R V hV=
    gaussianPhysicalFamilyIntegral η C W0 W1 (Finset.univ : Finset (∀i,slots i))
      (fun p=>compensationSubsetWeight η W Yp (fun i=>(p i).val) J)
      (fun p=>Ideal.span {slotProduct (fun i=>(p i).val) (Finset.univ\J)})
      (fun p=>X/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=>Y/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=>W i.val)
      (fun p i=>elementNorm (p i.val).val/Yp i.val) V hV U R := rfl

lemma lowCommonDyad_norm_of_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R B : ℝ) (degree : ℕ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ))
    (hb : ∀t : ℝ,‖∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
      compensationRowTest η C W0 W1 (fun i=>(p i).val) J X Y U t*
        selectedSlotFactor W Yp (fun i=>(p i).val) J t‖≤B*(1+‖t‖)^degree) :
    ‖lowCommonDyad η C W0 W1 slots W Yp J X Y U R V hV‖≤
      B*gaussianJointMoment V hV degree (U/R) := by
  let f := fun t : ℝ=>(∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
      compensationRowTest η C W0 W1 (fun i=>(p i).val) J X Y U t*
        selectedSlotFactor W Yp (fun i=>(p i).val) J t)*gaussianJointDensity V hV (U/R) t
  have hi := (JointLogSeparation.weighted_schwartz_integrable (gaussianJointDensity V hV (U/R)) degree).const_mul B
  have hmajor (t : ℝ) : ‖f t‖≤B*((1+‖t‖)^degree*‖gaussianJointDensity V hV (U/R) t‖) := by
    dsimp only [f]
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hb t)
      (norm_nonneg (gaussianJointDensity V hV (U/R) t))
  have hh := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hmajor)
  simpa only [f,lowCommonDyad,gaussianJointMoment,integral_const_mul] using hh

theorem low_central_gaussian_dyad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(U : ℝ),0<U→
      Z^(1+lowSelectedLength ell J-ε/2)≤U→U≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
    ∀(V : SchwartzMap ℝ ℂ)(hV : HasCompactSupport (V:ℝ→ℂ)),
      ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
        W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) U
          (Z^(1+lowSelectedLength ell J)) V hV‖≤
        C*Z^(3/16+254*ε)*gaussianJointMoment V hV degree (U/Z^(1+lowSelectedLength ell J)) := by
  obtain ⟨degree,C,hC,he⟩ := low_central_compensated_tuple η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J U hU hlo hhi W hW V hV
  apply lowCommonDyad_norm_of_bound
  intro t
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hZ.2 T hT hout hdis hnorm J U hU hlo hhi W hW t

end SevenEighths.ProbePhysical
end

end OAI

end Source1791

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGaussianRemote.lean; sha256: 1b8a49cf92868a2f64269607d0ef7edb1df20a04da83c27cd1a1985523987e42 -/
section Source1792
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma slotProduct_subtype {K : ℕ} (p : Fin K→O) (J : Finset (Fin K)) :
    slotProduct p J=∏i : J,p i.val := by rw [Finset.prod_coe_sort];rfl

lemma eventually_low_physical_scales {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤1/6) (b : ℝ) :
    ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
      ∀(slots : Fin K→Finset O),(∀i x,x∈slots i→x≠0)→
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(p : ∀i,slots i),
      1≤Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) ∧
      1≤Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) := by
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<(3/16:ℝ) by norm_num)).eventually
      (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro slots hn hnorm J p
  have hl : 0<elementNorm (slotProduct (fun i=>(p i).val) J) :=
    slotProduct_norm_pos _ (fun i=>hn i _ (p i).property) J
  have hb := lowUnselectedProduct_norm_bound ell hell hsum (max 1 b) Z (le_max_left _ _) hZ.le
    slots (fun i n hm=>(hnorm i n hm).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    J (fun i=>p i.val)
  rw [←slotProduct_subtype (fun i=>(p i).val) J] at hb
  have hLX : elementNorm (slotProduct (fun i=>(p i).val) J)≤Z^(17/48:ℝ) := by
    apply hb.trans
    calc
      _≤Z^(3/16:ℝ)*Z^(1/6:ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)];norm_num
  constructor
  · exact (one_le_div hl).mpr hLX
  · exact (one_le_div hl).mpr (hLX.trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))

lemma low_remote_power (Z ell ε : ℝ) (N : ℕ) (hZ : 1≤Z) (hell : ell≤1/6)
    (hN : 13/3≤(ε/2)*(N:ℝ)) :
    Z*(Z^(1+ell))^2/(Z^(ε/2))^N≤Z^(-1:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hsq : (Z^(1+ell))^2=Z^(2*(1+ell)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
    congr 1
    push_cast
    ring
  have hn : (Z^(ε/2))^N=Z^((ε/2)*(N:ℝ)) := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  rw [hsq,hn,show Z*Z^(2*(1+ell))=Z^(1+2*(1+ell)) by rw [Real.rpow_add hz,Real.rpow_one],←Real.rpow_sub hz]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

def lowRemote (Z ell ε T : ℝ) : Prop :=
  T/Z^(1+ell)≤(Z^(ε/2))⁻¹ ∨ Z^(ε/2)≤T/Z^(1+ell)

theorem low_remote_gaussian_dyads (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (b ε : ℝ) (hε : 0<ε) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(η : HeckeFamily.Character)(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖ else 0
      Summable f ∧ (∑'j : ℕ,f j)≤C*Z^(-1:ℝ) := by
  have hep : 0<ε/2 := by linarith
  obtain ⟨N,hN⟩ := exists_nat_gt ((13/3:ℝ)/(ε/2))
  have hN' : (13/3:ℝ)≤(ε/2)*(N:ℝ) := by
    have hh := (div_lt_iff₀ hep).mp hN
    nlinarith
  obtain ⟨Cg,hCg,he⟩ := gaussianPhysicalFamily_remote_polynomial V hV N
    a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  let q := elementNorm (calibrationForSet S hS).generator
  let C0 := Cg*(q*(128*max 1 b)^K)
  have hq : 0<q := calibration_elementNorm_pos _
  refine ⟨C0,by dsimp [C0];positivity,?_⟩
  filter_upwards [eventually_low_physical_scales ell hell hsum b] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro η T hT hnorm J W hW
  dsimp only [lowRemote]
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈canonicalSlotSupport (T i)→elementNorm n≤b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hs := hZ.2 _ hslots hnormE J
  have hh := he η S hS W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    hW0 hW1 hWB0 hWB1 (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
    (fun p=>compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J)
    (fun p=>Ideal.span {slotProduct (fun i=>(p i).val) (Finset.univ\J)})
    (fun p=>Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p=>Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p _=>(hs p).1) (fun p _=>(hs p).2)
    (fun i : SelectedSlot J=>W i.val) (fun p i=>elementNorm (p i.val).val/Z^(ell i.val))
    (Z^(1+lowSelectedLength ell J)) (Z^(ε/2)) (by positivity) (Real.one_le_rpow hZ.1.le hep.le)
  simp only [←lowCommonDyad_eq_family] at hh
  refine ⟨?_,?_⟩
  · convert hh.1 using 1
    funext j
    split_ifs with h <;> simp_all only [ite_true, ite_false]
  · have hhFinal := hh.2.trans (show _≤C0*Z^(-1:ℝ) from by
      have hm := compensation_scale_mass_bound η (calibrationForSet S hS) ell hell hsum b Z hZ.1.le T hT hnorm J W hW
      calc
        _≤Cg*((q*(128*max 1 b)^K)*Z)*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N := by gcongr
        _=C0*(Z*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N) := by dsimp [C0];ring
        _≤_ := mul_le_mul_of_nonneg_left (low_remote_power Z (lowSelectedLength ell J) ε N hZ.1.le
          (by have hb := lowLength_bounds ell hell hsum J;linarith) hN') (by dsimp [C0];positivity))
    convert hhFinal using 1
    apply tsum_congr
    intro j
    split_ifs with h <;> simp_all only [ite_true, ite_false]

end SevenEighths.ProbePhysical
end

end OAI

end Source1792

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGaussianCentral.lean; sha256: b283aa6bede21f0852977afe3fa894e9cff05b628c59abae4075efeb90c2f9b8 -/
section Source1793
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma not_lowRemote_bounds (Z ell ε U : ℝ) (hZ : 0<Z)
    (h : ¬lowRemote Z ell ε U) :
    Z^(1+ell-ε/2)≤U ∧ U≤Z^(1+ell+ε/2) := by
  simp only [lowRemote,not_or,not_le] at h
  apply lowCentral_ratio_bounds Z U ell ε hZ
  · have he : Z^(-ε/2)=(Z^(ε/2))⁻¹ := by
      rw [show -ε/2=-(ε/2) by ring,Real.rpow_neg hZ.le]
    rw [he]
    exact h.1.le
  · exact h.2.le

theorem low_central_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖
      Summable f ∧ (∑'j : ℕ,f j)≤C*Z^(3/16+256*ε) := by
  obtain ⟨degree,C,hC,he⟩ := low_central_gaussian_dyad η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  obtain ⟨Cm,hCm,hm⟩ := gaussianJointMoment_summed V hV degree ε hε
  refine ⟨C*Cm,mul_pos hC hCm,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  let R := Z^(1+lowSelectedLength ell J)
  let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
    ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
      W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j) R V hV‖
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  obtain ⟨hsm,hmb⟩ := hm R (by dsimp [R];positivity)
  have hb (j : ℕ) : f j≤(C*Z^(3/16+254*ε))*
      (((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := by
    dsimp only [f]
    split_ifs with hj
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (gaussianJointMoment_nonneg V hV degree _))
    · obtain ⟨hlo,hhi⟩ := not_lowRemote_bounds Z (lowSelectedLength ell J) ε ((2:ℝ)^j) hz hj
      apply (hZ.2 T hT hout hdis hnorm J ((2:ℝ)^j) (by positivity) hlo hhi W hW V hV).trans
      have hp : 1≤((2:ℝ)^j)^ε := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hε.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_mul_of_one_le_left (gaussianJointMoment_nonneg V hV degree _) hp
  have hn (j : ℕ) : 0≤f j := by dsimp [f];split_ifs <;>positivity
  have hsumf := Summable.of_nonneg_of_le hn hb (hsm.mul_left (C*Z^(3/16+254*ε)))
  refine ⟨hsumf,?_⟩
  calc
    _≤∑'j : ℕ,(C*Z^(3/16+254*ε))*(((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) :=
      hsumf.tsum_le_tsum hb (hsm.mul_left _)
    _=(C*Z^(3/16+254*ε))*(∑'j : ℕ,((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := tsum_mul_left
    _≤(C*Z^(3/16+254*ε))*(Cm*R^ε) := mul_le_mul_of_nonneg_left hmb (by positivity)
    _≤_ := by
      dsimp only [R]
      rw [←Real.rpow_mul hz.le]
      calc
        _=(C*Cm)*(Z^(3/16+254*ε)*Z^((1+lowSelectedLength ell J)*ε)) := by ring
        _≤_ := by
          rw [←Real.rpow_add hz]
          apply mul_le_mul_of_nonneg_left _ (mul_pos hC hCm).le
          have hh := lowLength_bounds ell hell hsum J
          exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by nlinarith)

end SevenEighths.ProbePhysical
end

end OAI

end Source1793

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGaussianSum.lean; sha256: 49657baf6a90f26fc2fda8654c53a3a65786030125130f0ede2c5fced7f12573 -/
section Source1794
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_dyad_norm_split (f : ℕ→ℂ) (p : ℕ→Prop) [DecidablePred p]
    (hc : Summable (fun j=>if p j then 0 else ‖f j‖))
    (hr : Summable (fun j=>if p j then ‖f j‖ else 0)) :
    Summable f ∧ ‖∑'j,f j‖≤(∑'j,if p j then 0 else ‖f j‖)+(∑'j,if p j then ‖f j‖ else 0) := by
  have he (j : ℕ) : ‖f j‖=(if p j then 0 else ‖f j‖)+(if p j then ‖f j‖ else 0) := by
    split_ifs <;>ring
  have hn : Summable (fun j=>‖f j‖) := (hc.add hr).congr (fun j=>(he j).symm)
  refine ⟨hn.of_norm,?_⟩
  apply (norm_tsum_le_tsum_norm hn).trans_eq
  exact (tsum_congr he).trans (hc.tsum_add hr)

theorem low_all_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV
      Summable f ∧ ‖∑'j : ℕ,f j‖≤C*Z^(3/16+256*ε) := by
  obtain ⟨Cc,hCc,hcentral⟩ := low_central_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 V hV W0 W1 a0 b0 a1 b1 B1 ha0 ha1 hab1 hB1 hW0 hW1 hW0s hW1s hWB1
  obtain ⟨Cr,hCr,hremote⟩ := low_remote_gaussian_dyads S hS ell hell hsum b ε hε V hV
    W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1 hW0 hW1 hWB0 hWB1
  refine ⟨Cc+Cr,add_pos hCc hCr,?_⟩
  filter_upwards [hcentral,hremote] with Z hc hr
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  have hc' := hc.2 T hT hout hdis hnorm J W hW
  have hr' := hr.2 η T hT (fun i P hP=>(hnorm i P hP).2) J W hW
  dsimp only at hc' hr' ⊢
  have hh := low_dyad_norm_split _ (fun j=>lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j)) hc'.1 hr'.1
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hp : Z^(-1:ℝ)≤Z^(3/16+256*ε) := Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith)
  calc
    _≤Cc*Z^(3/16+256*ε)+Cr*Z^(-1:ℝ) := add_le_add hc'.2 hr'.2
    _≤Cc*Z^(3/16+256*ε)+Cr*Z^(3/16+256*ε) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hCr.le)
    _=_ := by ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1794

/- Original source: OAI/NumberTheory/DirichletL/Detector/RayNormalization.lean; sha256: 87553b4b2eced80b5fa9d4b51bcd2b574fc26fd9532aaffa6e707d4016a1a462 -/
section Source1795
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeRayNormalization
open HeckeFamily ProbePhysical ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

theorem log_power_absorption (c ell d : ℝ) (hc : 0<c) (hell : 0<ell) (hd : 0<d) :
    ∀ᶠZ : ℝ in atTop,Z^(ell/6-d)≤c*(Z^ell)^(1/6:ℝ)/Real.log (Z^ell) := by
  have hh := (isLittleO_log_rpow_atTop hd).bound (div_pos hc hell)
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  have hZ0 : 0<Z := by linarith
  have hlog : 0<Real.log Z := Real.log_pos hZ1
  have hzd : 0<Z^d := Real.rpow_pos_of_pos hZ0 _
  have hb : ell*Real.log Z≤c*Z^d := by
    have hb' : Real.log Z≤(c/ell)*Z^d := by
      simpa only [Real.norm_eq_abs,abs_of_pos hlog,abs_of_pos hzd] using hZ
    calc
      _ ≤ ell*((c/ell)*Z^d) := mul_le_mul_of_nonneg_left hb' hell.le
      _ = _ := by field_simp
  rw [Real.log_rpow hZ0,←Real.rpow_mul hZ0.le]
  apply (le_div_iff₀ (mul_pos hell hlog)).mpr
  calc
    Z^(ell/6-d)*(ell*Real.log Z) ≤ Z^(ell/6-d)*(c*Z^d) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hZ0.le _)
    _ = c*Z^(ell*(1/6:ℝ)) := by
      rw [mul_left_comm,←Real.rpow_add hZ0]
      congr 1
      ring_nf

theorem principalScalar_inverse_of_slot_bounds {ι : Type*} (J : Finset ι)
    (ell mass : ι→ℝ) (Z d eps : ℝ) (hZ : 1≤Z) (_hd : 0≤d)
    (hbudget : d*J.card≤eps) (hm : ∀i∈J,Z^(ell i/6-d)≤mass i) :
    |(Probe.principalScalar J Z (∑i∈J,ell i) mass)⁻¹|≤Z^eps := by
  have hZ0 : 0<Z := by linarith
  have hm0 : ∀i∈J,0≤mass i := fun i hi=>(Real.rpow_nonneg hZ0.le _).trans (hm i hi)
  have hprod : Z^(∑i∈J,(ell i/6-d))≤∏i∈J,mass i := by
    rw [Real.rpow_sum_of_pos hZ0]
    exact Finset.prod_le_prod₀ (fun i _=>Real.rpow_nonneg hZ0.le _) hm
  have hn : |Probe.principalScalar J Z (∑i∈J,ell i) mass|=
      Z^(-(∑i∈J,ell i)/6)*(∏i∈J,mass i) := by
    unfold Probe.principalScalar
    rw [abs_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
      abs_of_pos (Real.rpow_pos_of_pos hZ0 _),abs_of_nonneg (Finset.prod_nonneg hm0)]
  have hpow : Z^(-(∑i∈J,ell i)/6)*Z^(∑i∈J,(ell i/6-d))=Z^(-d*J.card) := by
    rw [←Real.rpow_add hZ0]
    congr 1
    rw [Finset.sum_sub_distrib,←Finset.sum_div,Finset.sum_const,nsmul_eq_mul]
    ring
  have hl : Z^(-eps)≤|Probe.principalScalar J Z (∑i∈J,ell i) mass| := by
    calc
      _ ≤ Z^(-d*J.card) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
      _ = Z^(-(∑i∈J,ell i)/6)*Z^(∑i∈J,(ell i/6-d)) := hpow.symm
      _ ≤ _ := by rw [hn];exact mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hZ0.le _)
  rw [abs_inv]
  have hi := (inv_le_inv₀ ((Real.rpow_pos_of_pos hZ0 (-eps)).trans_le hl)
    (Real.rpow_pos_of_pos hZ0 (-eps))).mpr hl
  simpa only [Real.rpow_neg hZ0.le,inv_inv] using hi

variable (M : Id) [NeZero M]
local instance : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
include hH

theorem ray_slot_subpower_lower (S : Finset Id) (W : ℝ→ℝ)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) (hsupp : Function.support W⊆Set.Ioo a b)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W⊆Set.Ioi 0)
    (hW0 : ∀y,0≤W y) (hWne : W≠0) (ell d : ℝ) (hell : 0<ell) (hd : 0<d) :
    ∀ᶠZ : ℝ in atTop,Z^(ell/6-d)≤
      ∑P∈pool (RayQuotient.identityClass M H) S a b (Z^ell),
        W ((Ideal.absNorm P.val:ℝ)/(Z^ell))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
  obtain ⟨c,hc0,hbound⟩ := ray_pool_mass_eventually_lower_bound M H hH S W a b ha hab hsupp hW hc hp hW0 hWne
  filter_upwards [(tendsto_rpow_atTop hell).eventually hbound,log_power_absorption c ell d hc0 hell hd]
    with Z hZ hlog
  exact hlog.trans hZ

theorem ray_principalScalar_inverse_subpower {ι : Type*} (J : Finset ι)
    (S : Finset Id) (W : ι→ℝ→ℝ) (a b ell : ι→ℝ)
    (ha : ∀i∈J,0<a i) (hab : ∀i∈J,a i≤b i)
    (hsupp : ∀i∈J,Function.support (W i)⊆Set.Ioo (a i) (b i))
    (hW : ∀i∈J,ContDiff ℝ ∞ (W i)) (hc : ∀i∈J,HasCompactSupport (W i))
    (hp : ∀i∈J,tsupport (W i)⊆Set.Ioi 0)
    (hW0 : ∀i∈J,∀y,0≤W i y) (hWne : ∀i∈J,W i≠0) (hell : ∀i∈J,0<ell i)
    (eps : ℝ) (heps : 0<eps) :
    ∀ᶠZ : ℝ in atTop,
      |(Probe.principalScalar J Z (∑i∈J,ell i) (fun i=>
        ∑P∈pool (RayQuotient.identityClass M H) S (a i) (b i) (Z^(ell i)),
          W i ((Ideal.absNorm P.val:ℝ)/(Z^(ell i)))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ))))⁻¹|≤Z^eps := by
  let d : ℝ := eps/(J.card+1)
  have hd : 0<d := div_pos heps (by positivity)
  have hb : d*J.card≤eps := by
    dsimp [d]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : (0:ℝ)<J.card+1)]
    nlinarith
  have hm : ∀ᶠZ : ℝ in atTop,∀i∈J,Z^(ell i/6-d)≤
      ∑P∈pool (RayQuotient.identityClass M H) S (a i) (b i) (Z^(ell i)),
        W i ((Ideal.absNorm P.val:ℝ)/(Z^(ell i)))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
    apply (Filter.eventually_all_finset J).mpr
    intro i hi
    exact ray_slot_subpower_lower M H hH S (W i) (a i) (b i) (ha i hi) (hab i hi)
      (hsupp i hi) (hW i hi) (hc i hi) (hp i hi) (hW0 i hi) (hWne i hi) (ell i) d (hell i hi) hd
  filter_upwards [hm,eventually_ge_atTop (1:ℝ)] with Z hmass hZ
  exact principalScalar_inverse_of_slot_bounds J ell _ Z d eps hZ hd.le hb hmass

end SevenEighths.ProbeRayNormalization
end

end OAI

end Source1795

/- Original source: OAI/NumberTheory/DirichletL/Detector/RayPoolDisjoint.lean; sha256: eec96f4c382be0cadee250ac904cd2ce20aefbf4a882b8caf7d681486b1915af -/
section Source1796
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical
local notation "Id" => Ideal HeckeFamily.O

lemma annular_power_separation (a b r s : ℝ) (ha : 0<a) (hrs : r<s) :
    ∀ᶠZ : ℝ in atTop,b*Z^r<a*Z^s := by
  have hh := (tendsto_rpow_atTop (show 0<s-r by linarith)).eventually (eventually_gt_atTop (b/a))
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  have ht : b<a*Z^(s-r) := by
    have h := (div_lt_iff₀ ha).mp hZ
    nlinarith
  have hp : 0<Z^r := Real.rpow_pos_of_pos hZ0 _
  calc
    b*Z^r < (a*Z^(s-r))*Z^r := mul_lt_mul_of_pos_right ht hp
    _=a*Z^s := by rw [mul_assoc,←Real.rpow_add hZ0];congr 1;congr 1;ring

theorem power_pools_eventually_disjoint {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (a b ell : ι→ℝ)
    (ha : ∀i,0<a i) (hab : ∀i,a i≤b i) (hell : Function.Injective ell) :
    ∀ᶠZ : ℝ in atTop,∀i j, i≠j→Disjoint (pool C S (a i) (b i) (Z^(ell i)))
      (pool C S (a j) (b j) (Z^(ell j))) := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i=j
  · exact Filter.Eventually.of_forall (fun Z hn=>(hn hij).elim)
  have hne : ell i≠ell j := fun h=>hij (hell h)
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · filter_upwards [annular_power_separation (a j) (b i) (ell i) (ell j) (ha j) hlt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith
  · filter_upwards [annular_power_separation (a i) (b j) (ell j) (ell i) (ha i) hgt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith

theorem power_pool_tuples_eventually_injective {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (a b ell : ι→ℝ)
    (ha : ∀i,0<a i) (hab : ∀i,a i≤b i) (hell : Function.Injective ell) :
    ∀ᶠZ : ℝ in atTop,∀P:(∀i,pool C S (a i) (b i) (Z^(ell i))),
      Function.Injective (fun i=>(P i).val) := by
  filter_upwards [power_pools_eventually_disjoint C S a b ell ha hab hell] with Z hZ P
  intro i j heq
  by_contra hn
  have hq : (P i).val=(P j).val := heq
  exact Finset.disjoint_left.mp (hZ i j hn) (P i).property (by rw [hq];exact (P j).property)
end SevenEighths.ProbeRaySlots
end

end OAI

end Source1796

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowCommonBound.lean; sha256: ea03172e8ef66b2fbd0ba0526704dbdfee44c241906d8c9bace5f3b84d636c22 -/
section Source1797
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_window_log_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (y : ℝ) (hy : W (Real.exp y)≠0) :
    |y|≤|Real.log a|+|Real.log b| := by
  have hs := hW hy
  have hlo := Real.log_le_log ha hs.1
  have hhi := Real.log_le_log (Real.exp_pos y) hs.2
  rw [Real.log_exp] at hlo hhi
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)],
    by linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]⟩

theorem compensatedPhysicalProbe_low (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
      ‖compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
        (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(ell i))
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤C*Z^(3/16+256*ε) := by
  obtain ⟨V,hV,hbudget,hidentity⟩ := compensatedPhysicalProbe_common_gaussian W
    (fun _=>|Real.log a|+|Real.log b|) (fun _=>by positivity)
    (fun i=>low_window_log_support (W i) a b ha (hW i))
  choose C hC he using fun A : Finset (Fin K)=>low_all_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 (V A) (hV A) W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  let C0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,C A)+1
  have hC0 : 0<C0 := by
    have hn := Finset.sum_nonneg (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=>(hC A).le)
    dsimp only [C0]
    linarith
  refine ⟨C0,hC0,?_⟩
  filter_upwards [Filter.eventually_all.mpr he] with Z hZ
  have hz1 : 1<Z := (hZ ∅).1
  have hz : 0<Z := lt_trans zero_lt_one hz1
  refine ⟨hz1,?_⟩
  intro T hT hout hdis hnorm
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  rw [hidentity η (calibrationForSet S hS) W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    _ hslots (fun i=>Z^(ell i)) (fun i=>by positivity)
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hz]
  apply (norm_sum_le _ _).trans
  have hterm (A : Finset (Fin K)) :
      ‖∑'j : ℕ,lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i)) W
        (fun i=>Z^(ell i)) A (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j)
        (Z*∏i∈Finset.univ\A,Z^(ell i)) (V A) (hV A)‖≤C A*Z^(3/16+256*ε) := by
    have hc : Z*(∏i∈Finset.univ\A,Z^(ell i))=Z^(1+lowSelectedLength ell A) := by
      rw [lowSelectedScale_product ell A Z hz,Real.rpow_add hz,Real.rpow_one]
    rw [hc]
    exact ((hZ A).2 T hT hout hdis hnorm A W hWnorm).2
  have hh := Finset.sum_le_sum (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=>hterm A)
  apply hh.trans
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by dsimp [C0];linarith) (Real.rpow_nonneg hz.le _)

theorem original_ray_compensatedPhysicalProbe_low (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤1/6) (R : Set Id)
    (a b ε : ℝ) (ha : 0<a) (hab : a≤b) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤C*Z^(3/16+256*ε) := by
  obtain ⟨C,hC,he⟩ := compensatedPhysicalProbe_low η S hmax hS.bad ell hell hsum
    a b ε ha hε hε1 W hW hWnorm W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨C,hC,?_⟩
  filter_upwards [he,ProbeRaySlots.power_pools_eventually_disjoint R S (fun _=>a) (fun _=>b) ell
    (fun _=>ha) (fun _=>hab) hinj] with Z hZ hd
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  apply hZ.2 _ (fun i=>ProbeRaySlots.pool_supported R S hS a b (Z^(ell i)))
    (fun i P hP=>((ProbeRaySlots.mem_pool R S a b (Z^(ell i)) P).mp hP).2.2.2)
    (fun i j hij=>hd i j hij)
  intro i P hP
  have hh := ProbeRaySlots.pool_norm_bounds R S ha.le hab (Real.rpow_pos_of_pos hz _) P hP
  simpa only [mul_comm] using And.intro hh.1.le hh.2

end SevenEighths.ProbePhysical
end

end OAI

end Source1797

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowWindowBound.lean; sha256: 680f8b3f8c85f574ba13982ea4962491fc47d163a0f10fb795aff7db948e3e18 -/
section Source1798
namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma compensatedPhysicalProbe_window_scale {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (X Y Z : ℝ) (c : ℂ) :
    compensatedPhysicalProbe η C W0 W1 slots (fun i x=>c*W i x) Yp X Y Z=
      c^K*compensatedPhysicalProbe η C W0 W1 slots W Yp X Y Z := by
  unfold compensatedPhysicalProbe
  simp_rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_assoc]
  exact (Finset.mul_sum ..).symm

theorem original_ray_compensatedPhysicalProbe_low_loss
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤1/6) (R : Set Id)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤B)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤C*Z^(3/16+loss) := by
  let D := max 1 B
  have hD : 0<D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDc : (D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hD.ne'
  let Wn := fun i x=>W i x/(D:ℂ)
  have hWn : ∀i,Function.support (Wn i)⊆Set.Icc a b := by
    intro i x hx
    apply hW i
    intro hz
    exact hx (by dsimp [Wn];rw [hz,zero_div])
  have hn : ∀i x,‖Wn i x‖≤1 := by
    intro i x
    dsimp only [Wn]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
    exact (div_le_one hD).mpr ((hWnorm i x).trans (le_max_right _ _))
  have hscale : (fun i x=>(D:ℂ)*Wn i x)=W := by
    funext i x
    dsimp [Wn]
    field_simp
  let ε := min (loss/512) (1/2)
  have he : 0<ε := by dsimp [ε];positivity
  have he1 : ε<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have heloss : 256*ε≤loss := by have hh := min_le_left (loss/512) (1/2:ℝ);dsimp only [ε];linarith
  intro η
  obtain ⟨C,hC,hbound⟩ := original_ray_compensatedPhysicalProbe_low η S hS hmax ell hell hinj hsum R
    a b ε ha hab he he1 Wn hWn hn W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨D^K*C,by positivity,?_⟩
  filter_upwards [hbound,Filter.eventually_ge_atTop (1:ℝ)] with Z hb hZ
  have heq := compensatedPhysicalProbe_window_scale η (calibrationForSet S hmax) W0 W1
    (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) Wn (fun i=>Z^(ell i))
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (D:ℂ)
  rw [hscale] at heq
  rw [heq,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
  calc
    _≤D^K*(C*Z^(3/16+256*ε)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _≤D^K*(C*Z^(3/16+loss)) := by gcongr
    _=_ := by ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1798

/- Original source: OAI/NumberTheory/DirichletL/Detector/PrincipalInput.lean; sha256: 9e0b2065602d1db2574b5e5aa2a6c50e7096d44f04870994c9604a9f2b09834b -/
section Source1799
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeMellinBoundary
open PrincipalMellinResidues ProbeFiniteProductBounds
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma principalTuple_source_integrand {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (P : Fin K→PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    sourceMellinWeight W0 W1 X Y Z x w z*
      (∏i,(elementNorm (primaryGenerator (P i).val):ℂ)^(z-1))*
      indexedCompensatedHigh η S (fun i=>primaryGenerator (P i).val) 1 x w z=
    sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) x
      (globalClosedCorrection η S x) (slotMultiplier η Finset.univ (fun i=>{P i}) (fun _ _=>1) x) w z*
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w := by
  have hnorm (i : Fin K) : (elementNorm (primaryGenerator (P i).val):ℂ)=(Ideal.absNorm (P i).val:ℂ) := by
    rw [primaryTuple_norm (P i) (outside_prime_supported S hS.bad (P i) (hPS i))]
    norm_cast
  rw [indexedCompensatedHigh_principal_continued η S hS P hP hPS x w z hx hw hz]
  unfold sourceMultiplier sourceMellinWeight
  simp only [hnorm,slotMultiplier,Finset.sum_singleton,one_mul,localMultiplier,
    Complex.ofReal_natCast,Finset.prod_mul_distrib]
  ring

theorem principalRowIntegral_eq_sourceMultiplier {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (P : Fin K→PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    principalRowIntegral η S (fun i=>primaryGenerator (P i).val) W0 W1 X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((3:ℂ)+t.1.1*Complex.I)
          (globalClosedCorrection η S ((3:ℂ)+t.1.1*Complex.I))
          (slotMultiplier η Finset.univ (fun i=>{P i}) (fun _ _=>1) ((3:ℂ)+t.1.1*Complex.I))
          ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*((2:ℂ)+t.1.2*Complex.I))*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+t.2*Complex.I) ∂heightMeasure := by
  unfold principalRowIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  exact principalTuple_source_integrand η S hS P hP hPS W0 W1 X Y Z
    ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])

end SevenEighths.ProbePhysical
end

end OAI

end Source1799
