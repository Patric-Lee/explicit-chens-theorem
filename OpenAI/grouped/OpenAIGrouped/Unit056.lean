import OpenAIGrouped.Unit029
import OpenAIGrouped.Unit055
import OpenAIGrouped.Unit030
import OpenAIGrouped.Unit008
import OpenAIGrouped.Unit017
import OpenAIGrouped.Unit031
import OpenAIGrouped.Unit026
import OpenAIGrouped.Unit032
import OpenAIGrouped.Unit033
import OpenAIGrouped.Unit044
import OpenAIGrouped.Unit045

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsCentralTerms.lean; sha256: 1dc96de56d0f64bba14ba663b728aba48943aaa3ce25cc8b0dfb6e1f2e3eb987 -/
section Source2240
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
theorem sourceRowTerm_central_nonstrict (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1))
    (hstrict : ¬(e=1 ∧ l=0 ∧ k=1 ∧ m=0)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2-x.re) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ : 0<Q := by
    dsimp only [Q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hm0 : (0:ℝ)≤m := Nat.cast_nonneg m
  have hzpos : 0<z.re := by rw [hz];norm_num
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
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 5 (1/2-x.re)
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_left hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^5≤2*Q^5 by nlinarith [pow_nonneg hQ.le 5])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          linarith
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 6 (1/2-x.re)
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
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 1 m 6 (1/2-x.re)
        · have hs := nonprincipal_kone_norm p hp hg hc 5 (j+6*m) (by decide) (by decide)
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 0 m (1/2) (1/2-x.re)
      · have hs := nonprincipal_kzero_norm p hp hg hc 0 (j+6*m) (by decide)
        simp only [pow_zero,one_mul,Real.sqrt_eq_rpow] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 0 (by decide),Nat.reduceSub] using hs.trans (hrelax (1/2))
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · have hm : m≠0 := by intro hm;exact hstrict ⟨rfl,rfl,rfl,hm⟩
      apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 1 m (3/2) (1/2-x.re)
      · have hs := positiveScalar_norm_le p hp hg hc 0 1 (j+6*m) (by decide)
        simp only [Nat.zero_add,pow_one] at hs
        have he : 2*Q*Real.sqrt Q=2*Q^(3/2:ℝ) := by
          have ht := pow_mul_sqrt Q hQ 1
          norm_num at ht
          rw [mul_assoc,ht]
        rw [he] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 1 (by decide),Nat.reduceSub] using hs
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        nlinarith [hzm1 hm]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 0 m (5/2) (1/2-x.re)
      · have hs := nonprincipal_kzero_norm p hp hg hc 2 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (5/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 1 m 3 (1/2-x.re)
      · have hs := nonprincipal_kone_norm p hp hg hc 2 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 3 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^3≤2*Q^3 by nlinarith [pow_nonneg hQ.le 3])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 0 m (7/2) (1/2-x.re)
      · have hs := nonprincipal_kzero_norm p hp hg hc 3 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (7/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 1 m 4 (1/2-x.re)
      · have hs := nonprincipal_kone_norm p hp hg hc 3 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 4 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^4≤2*Q^4 by nlinarith [pow_nonneg hQ.le 4])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith

end SevenEighths.ProbeEuler
end

end OAI

end Source2240

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsCentralBase.lean; sha256: 763b0be49968c271226bbac5a96dc6e2e8bf7d5a973754091e6513afc61e4d38 -/
section Source2241
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma rowBaseFinite_central_remainder (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j e l : ℕ) (hj : j<6)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let T := fun k m=>rowMarkedTerm p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l k m
    ‖rowBaseFinite p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l-
      (if e=1 ∧ l=0 then T 1 0 else 0)‖≤16*Q^(1/2-x.re) := by
  dsimp only
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  let T := fun k m=>rowMarkedTerm p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l k m
  have hpow : 0≤Q^(1/2-x.re) := by positivity
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_V_half _ hQ z (by rw [hz]))
  have ht (k m : ℕ) (hk : k≤1) (hstrict : ¬(e=1 ∧ l=0 ∧ k=1 ∧ m=0)) :
      ‖T k m‖≤2*Q^(1/2-x.re) := by
    have ht0 : e+3*l≠0 := by rcases hf with h|h|h|h <;> omega
    dsimp only [T,Q]
    simp only [Complex.ofReal_natCast]
    rw [←sourceRowTerm_pos p hp hg eta a rho x w z j e l k m ht0]
    exact sourceRowTerm_central_nonstrict p hp hg hc eta a rho x w z alpha eps
      heta ha hρ halpha halpha1 heps heps1 hx hw hz j e l k m hj hk hf hstrict
  have hd (k : ℕ) (hk : k≤1) : ‖T k 2/(1-coordV Q z)‖≤4*Q^(1/2-x.re) := by
    rw [div_eq_mul_inv,norm_mul]
    exact (mul_le_mul (ht k 2 hk (by omega)) hv (norm_nonneg _) (by positivity)).trans_eq (by ring)
  by_cases hb : e=1 ∧ l=0
  · rw [ite_eq_left hb]
    have hid : rowBaseFinite p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l-T 1 0=
        ((T 0 0+T 0 1+T 0 2/(1-coordV Q z))+T 1 1)+T 1 2/(1-coordV Q z) := by
      simp only [rowBaseFinite,Fin.sum_univ_two]
      dsimp only [T]
      norm_num only [Fin.val_zero,Fin.val_one]
      ring
    change ‖rowBaseFinite p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l-T 1 0‖≤_
    rw [hid]
    have h00 := ht 0 0 (by omega) (by omega)
    have h01 := ht 0 1 (by omega) (by omega)
    have h11 := ht 1 1 (by omega) (by omega)
    have hn := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h00 h01)) (hd 0 (by omega)))) h11)) (hd 1 (by omega)))
    exact hn.trans (by linarith)
  · rw [ite_eq_right hb,sub_zero]
    unfold rowBaseFinite
    apply (norm_sum_le _ _).trans
    calc
      _≤∑ _k : Fin 2,8*Q^(1/2-x.re) := by
        apply Finset.sum_le_sum
        intro k hk
        have h0 := ht k.val 0 (by omega) (by tauto)
        have h1 := ht k.val 1 (by omega) (by omega)
        exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h0 h1)) (hd k.val (by omega)))).trans_eq (by ring)
      _=16*Q^(1/2-x.re) := by simp;ring

include hc in
theorem rowClosedMarked_central_remainder (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let R := evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z)
    let T := rowMarkedTerm p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j 1 0 1 0
    ‖rowClosedMarked p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j-T/(1-R)‖≤
      128*Q^(1/2-x.re) := by
  dsimp only
  have h02 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 0 2 hj (by omega)
  have h10 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 1 0 hj (by omega)
  have h01 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 0 1 hj (by omega)
  have h11 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 1 1 hj (by omega)
  dsimp only at h02 h10 h01 h11
  norm_num only [and_true,true_and,and_false,false_and,Nat.reduceEqDiff,ite_true,ite_false,sub_zero] at h02 h10 h01 h11
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha (by rw [hx];linarith) (by rw [hz]))
  simp only [Complex.ofReal_natCast] at *
  unfold rowClosedMarked
  rw [←sub_div,div_eq_mul_inv,norm_mul]
  have heq (A B C D T : ℂ) : A+B+C+D-T=A+(B-T)+C+D := by ring
  rw [heq]
  apply (mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  calc
    _≤(16*(_ : ℝ)+16*_+16*_+16*_)*2 := mul_le_mul_of_nonneg_left hr (by positivity)
    _=_ := by ring
end SevenEighths.ProbeEuler
end

end OAI

end Source2241

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsCentralStrict.lean; sha256: 4c4cbd363da475961b016844b8bb21776ac3551e63be9316d32d87df59360e49 -/
section Source2242
namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
lemma squarefree_base_boundary_norm (j : ℕ) (hj : j≤1) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 0 1 j‖≤
      Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  have he := row_squarefree_kone p hp hg hc 0 0 j (by omega)
  norm_num only [Nat.mul_zero,zero_add,mul_zero,add_zero,pow_zero,one_mul] at he
  rw [he,ite_eq_right (by omega)]
  split_ifs
  · rw [norm_mul,norm_mul,norm_inv,
      Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide),
      inv_one,one_mul,primeGauss_actual_norm p hp.ne_zero hg hc]
    norm_num
  · simp only [mul_zero,norm_zero]
    positivity

include hc in
lemma squarefree_base_strict_norm (j : ℕ) (hj : j<6) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 0 1 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by
  have he := row_squarefree_kone p hp hg hc 0 0 j hj
  norm_num only [Nat.mul_zero,zero_add,mul_zero,add_zero,pow_zero,one_mul] at he
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hQ1 : (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le
      ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩
    change 2≤Ideal.absNorm (Ideal.span {p}) at hh
    exact_mod_cast (show 1≤Ideal.absNorm (Ideal.span {p}) by omega)
  have hfac : ‖if 1<j then (Ideal.absNorm (Ideal.span {p}):ℂ)-1 else if j=1 ∧ True then -(1:ℂ) else 0‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    split_ifs
    · rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (by linarith)]
      linarith
    · simpa using hQ1
    · simp
  rw [he,norm_mul,norm_mul,norm_inv,
    Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide),
    inv_one,one_mul,primeGauss_actual_norm p hp.ne_zero hg hc]
  calc
    _≤Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ)*(Ideal.absNorm (Ideal.span {p}):ℝ) :=
      mul_le_mul_of_nonneg_left hfac (Real.sqrt_nonneg _)
    _=(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by
      rw [mul_comm]
      convert ProbeEuler.pow_mul_sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) hQ 1 using 1 <;> norm_num
end SevenEighths.ProbePrimePower
end

end OAI

end Source2242

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsCentralEntry.lean; sha256: 0d39c172997b49257e34fdb76f412399c4f203be884369727dc1e3fba979ac4c -/
section Source2243
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma sourceRowTerm_central_strict_norm (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1) (j : ℕ) (hj : j<6) :
    ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1-x.re-w.re) := by
  apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ
    j 1 0 1 0 (3/2) (1-x.re-w.re)
  · have hb := squarefree_base_strict_norm p hp hg hc j hj
    have ht : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by positivity
    simpa only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,ite_false,
      Nat.reduceEqDiff,mul_zero,add_zero] using hb.trans (show _≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) by linarith)
  · norm_num ; linarith

include hc in
lemma sourceRowTerm_central_boundary_norm (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1) (j : ℕ) (hj : j≤1) :
    ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re-w.re) := by
  apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ
    j 1 0 1 0 (1/2) (-x.re-w.re)
  · have hb := squarefree_base_boundary_norm p hp hg hc j hj
    rw [Real.sqrt_eq_rpow] at hb
    have ht : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) := by positivity
    simpa only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,ite_false,
      Nat.reduceEqDiff,mul_zero,add_zero] using hb.trans (show _≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) by linarith)
  · norm_num
end SevenEighths.ProbeEuler
end

end OAI

end Source2243

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsCentralRamified.lean; sha256: cb213e5903bdea0f731b65b5cd3f3031fa06ae8922ffdeda1f6235e3b5b8557f -/
section Source2244
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedStrictSelected (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    (rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j 1 0 1 0 /
      (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        (coordV (Ideal.absNorm (Ideal.span {p})) z)))

include hc in
theorem ramifiedSelected_central_regular (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x w z j-ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      385*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0<Q := by dsimp [Q];linarith
  have hQ1 : 1≤Q := by linarith
  have hrem := rowClosedMarked_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  dsimp only at hrem
  simp only [Complex.ofReal_natCast] at hrem
  have hH := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z hQ heta ha hρ
    (by rw [hx];linarith) (by rw [hw];linarith) (by rw [hz]) (by rw [hx,hw];linarith) j hj
  have hV := first_region_V_half _ hQ z (by rw [hz])
  have h1V : ‖1-coordV Q z‖≤3/2 := by
    have h := norm_sub_le (1:ℂ) (coordV Q z)
    rw [norm_one] at h
    change ‖coordV Q z‖≤1/2 at hV
    linarith
  have hphase : ‖star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x‖≤Q^x.re := by
    rw [norm_mul,norm_star,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hqw : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)‖≤Q^(1/2:ℝ) := by
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
  have hid (B V M T q H : ℂ) : B*V*M-q*H-B*V*T=B*V*(M-T)-q*H := by ring
  unfold ramifiedSelected ramifiedStrictSelected
  rw [hid]
  apply (norm_sub_le _ _).trans
  simp only [norm_mul] at hphase ⊢
  calc
    _≤(Q^x.re*(3/2))*(128*Q^(1/2-x.re))+Q^(1/2:ℝ)*193 := by
      gcongr
    _=385*Q^(1/2:ℝ) := by
      have ht : Q^x.re*Q^(1/2-x.re)=Q^(1/2:ℝ) := by rw [←Real.rpow_add hQ0];congr 1;ring
      nlinarith [ht]
end SevenEighths.ProbeEuler
end

end OAI

end Source2244

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsCentralStrictSelected.lean; sha256: d4f77f1a73bb948272eb58d696ad4876d90a065e10a9d9473d0d00d66ee22642 -/
section Source2245
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma ramifiedStrictSelected_from_entry (eta a rho x w z : ℂ) (j : ℕ) (b : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (heta : ‖eta‖≤1) (ha : ‖a‖≤1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (ht : ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^b) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(x.re+b) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0<Q := by dsimp [Q];linarith
  rw [sourceRowTerm_pos p hp hg eta a rho x w z j 1 0 1 0 (by omega)] at ht
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha hx hz)
  simp only [Complex.ofReal_natCast] at hr
  have hv := first_region_V_half _ hQ z hz
  have hs := norm_sub_le (1:ℂ) (coordV Q z)
  rw [norm_one] at hs
  have h1V : ‖1-coordV Q z‖≤3/2 := by change ‖coordV Q z‖≤1/2 at hv;linarith
  have hphase : ‖star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x‖≤Q^x.re := by
    rw [norm_mul,norm_star,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  unfold ramifiedStrictSelected
  rw [div_eq_mul_inv]
  simp only [norm_mul] at hphase ⊢
  calc
    _≤(Q^x.re*(3/2))*((2*Q^b)*2) := by gcongr
    _=6*Q^(x.re+b) := by rw [Real.rpow_add hQ0];ring

include hc in
theorem ramifiedStrictSelected_central_norm (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1-w.re) := by
  have hb := ramifiedStrictSelected_from_entry p hp hg eta a rho x w z j (1-x.re-w.re)
    hQ heta ha hx hz (sourceRowTerm_central_strict_norm p hp hg hc eta a rho x w z heta ha hρ j hj)
  convert hb using 1 ; congr 2 ; ring

include hc in
theorem ramifiedStrictSelected_boundary_norm (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j≤1) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-w.re) := by
  have hb := ramifiedStrictSelected_from_entry p hp hg eta a rho x w z j (-x.re-w.re)
    hQ heta ha hx hz (sourceRowTerm_central_boundary_norm p hp hg hc eta a rho x w z heta ha hρ j hj)
  convert hb using 1 ; congr 2 ; ring
end SevenEighths.ProbeEuler
end

end OAI

end Source2245

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsCentralDefect.lean; sha256: 8c28ef550ba8b3e5d607fd48f4fc95def6a27d2818c46833909573df240d34cd -/
section Source2246
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
lemma rowClosedMarked_central_size (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤
      132*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ1 : 1≤Q := by dsimp [Q];linarith
  have hrem := rowClosedMarked_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  dsimp only at hrem
  simp only [Complex.ofReal_natCast] at hrem
  have ht := sourceRowTerm_central_strict_norm p hp hg hc eta a rho x w z heta ha hρ j hj
  rw [sourceRowTerm_pos p hp hg eta a rho x w z j 1 0 1 0 (by omega)] at ht
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha (by rw [hx];linarith) (by rw [hz]))
  have he : Q^(1-x.re-w.re)=Q^(-10*eps) := by congr 1;rw [hx,hw];ring
  have hn : Q^(1/2-x.re)≤Q^(-10*eps) := Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hx];linarith)
  have hdiv : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV Q z) rho j 1 0 1 0 /
      (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV Q z))‖≤4*Q^(-10*eps) := by
    rw [div_eq_mul_inv,norm_mul]
    have hh := mul_le_mul ht hr (norm_nonneg _) (by positivity)
    exact hh.trans_eq (by change (2*Q^(1-x.re-w.re))*2=4*Q^(-10*eps);rw [he];ring)
  dsimp only [Q] at hdiv
  have hh := (norm_add_le _ _).trans (add_le_add hrem hdiv)
  simp only [sub_add_cancel] at hh
  exact hh.trans (by change 128*Q^(1/2-x.re)+4*Q^(-10*eps)≤132*Q^(-10*eps);nlinarith)

include hc in
theorem ramifiedClosed_central_defect (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    ‖ramifiedClosed p hp hg eta a rho x w z j-1‖≤
      198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps) := by
  have hb := rowClosedMarked_central_size p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hv := first_region_V_half _ hQ z (by rw [hz])
  have hs := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
  rw [norm_one] at hs
  unfold ramifiedClosed
  rw [add_sub_cancel_left,norm_mul]
  apply (mul_le_mul (show ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 by linarith)
    hb (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)).trans_eq
  ring
end SevenEighths.ProbeEuler
end

end OAI

end Source2246

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsCentralLower.lean; sha256: 9bd906af49b4a5f6533d6857700def19df6c6d61588ba425b07190022128cad7 -/
section Source2247
namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

theorem central_correction_threshold (eps : ℝ) (heps : 0<eps) :
    ∃Q0 : ℝ,480≤Q0 ∧ ∀Q : ℝ,Q0≤Q→198*Q^(-10*eps)≤1/2 := by
  have hh : Tendsto (fun Q : ℝ=>198*Q^(-10*eps)) atTop (nhds 0) := by
    simpa only [mul_zero,neg_mul] using
      (tendsto_rpow_neg_atTop (show 0<10*eps by positivity)).const_mul (198:ℝ)
  have he := hh.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  obtain ⟨Q0,hQ0⟩ := Filter.eventually_atTop.mp he
  refine ⟨max 480 Q0,le_max_left _ _,?_⟩
  intro Q hQ
  exact (hQ0 Q ((le_max_right _ _).trans hQ)).le

variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
theorem ramifiedClosed_central_lower (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (hsmall : 198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps)≤1/2)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    1/2≤‖ramifiedClosed p hp hg eta a rho x w z j‖ := by
  have hd := ramifiedClosed_central_defect p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hh := norm_add_le (1-ramifiedClosed p hp hg eta a rho x w z j)
    (ramifiedClosed p hp hg eta a rho x w z j)
  rw [sub_add_cancel,norm_one,norm_sub_rev] at hh
  linarith
end SevenEighths.ProbeEuler
end

end OAI

end Source2247

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsCentralRamifiedQuotient.lean; sha256: 77b3b626606f126fc6a1addacd0d61dc68653a7497f92fb6bfe7f79ce097273f -/
section Source2248
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma norm_div_le_twice (A H : ℂ) (hH : 1/2≤‖H‖) : ‖A/H‖≤2*‖A‖ := by
  rw [norm_div]
  apply (div_le_iff₀ (by linarith : 0<‖H‖)).mpr
  nlinarith [norm_nonneg A]

variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
theorem ramifiedSelected_central_quotient (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (hsmall : 198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps)≤1/2)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    Q^(-1:ℝ)*‖ramifiedSelected p hp hg eta a rho x w z j /
      ramifiedClosed p hp hg eta a rho x w z j‖≤
      800*Q^(-(1/2:ℝ))+(if 2≤j then 12*Q^(-w.re) else 0) := by
  dsimp only
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0<Q := by dsimp [Q];linarith
  have hQ1 : 1≤Q := by linarith
  have hH := ramifiedClosed_central_lower p hp hg hc eta a rho x w z alpha eps hQ hsmall heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hreg := ramifiedSelected_central_regular p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hnorm := norm_div_le_twice (ramifiedSelected p hp hg eta a rho x w z j)
    (ramifiedClosed p hp hg eta a rho x w z j) hH
  have htri := (norm_add_le _ _).trans (add_le_add hreg (le_refl ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖))
  rw [sub_add_cancel] at htri
  have hpow : Q^(-1:ℝ)*Q^(1/2:ℝ)=Q^(-(1/2:ℝ)) := by rw [←Real.rpow_add hQ0];norm_num
  have hqi : 0≤Q^(-1:ℝ) := Real.rpow_nonneg hQ0.le _
  by_cases hj2 : 2≤j
  · rw [ite_eq_left hj2]
    have hs := ramifiedStrictSelected_central_norm p hp hg hc eta a rho x w z hQ heta ha hρ
      (by rw [hx];linarith) (by rw [hz]) j hj
    have hb : ‖ramifiedSelected p hp hg eta a rho x w z j‖≤385*Q^(1/2:ℝ)+6*Q^(1-w.re) := by linarith
    have hprod : Q^(-1:ℝ)*Q^(1-w.re)=Q^(-w.re) := by rw [←Real.rpow_add hQ0];congr 1;ring
    calc
      _≤Q^(-1:ℝ)*(2*(385*Q^(1/2:ℝ)+6*Q^(1-w.re))) := mul_le_mul_of_nonneg_left (hnorm.trans (by linarith)) hqi
      _=770*Q^(-(1/2:ℝ))+12*Q^(-w.re) := by nlinarith [hpow,hprod]
      _≤_ := by nlinarith [Real.rpow_nonneg hQ0.le (-(1/2:ℝ))]
  · rw [ite_eq_right hj2,add_zero]
    have hs := ramifiedStrictSelected_boundary_norm p hp hg hc eta a rho x w z hQ heta ha hρ
      (by rw [hx];linarith) (by rw [hz]) j (by omega)
    have hqw : Q^(-w.re)≤Q^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
    have hb : ‖ramifiedSelected p hp hg eta a rho x w z j‖≤391*Q^(1/2:ℝ) := by nlinarith
    calc
      _≤Q^(-1:ℝ)*(2*(391*Q^(1/2:ℝ))) := mul_le_mul_of_nonneg_left (hnorm.trans (by linarith)) hqi
      _=782*Q^(-(1/2:ℝ)) := by nlinarith [hpow]
      _≤_ := mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hQ0.le _)
end SevenEighths.ProbeEuler
end

end OAI

end Source2248

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CentralRamified.lean; sha256: fc83e69dc7c0f72a966a9a83d3672879bc193f9b62d09609797fc6a3ac579eb4 -/
section Source2249
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge

theorem actual_central_ramified_normalized (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤P.val.absNorm)
    (alpha eps : ℝ) (x w z : ℂ)
    (hsmall : 198*(P.val.absNorm:ℝ)^(-10*eps)≤1/2)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50) :
    1/2≤‖ramifiedCorrection η u P hs x w z‖ ∧
    (P.val.absNorm:ℝ)^(-1:ℝ)*
      ‖continuedCompensatedLocal η u P hs x w z
        (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
        ramifiedCorrection η u P hs x w z‖≤
      800*(P.val.absNorm:ℝ)^(-(1/2:ℝ))+
        (if 2≤multiplicity (primaryGenerator P.val) u.val then 12*(P.val.absNorm:ℝ)^(-w.re) else 0) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal HeckeFamily.O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  have hρ := actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)
  have hnorm : Ideal.absNorm (Ideal.span {p})=P.val.absNorm := congrArg Ideal.absNorm hspan
  constructor
  · have hb := ramifiedClosed_central_lower p hp hg.1 hg.2 _ _ _ x w z alpha eps
      (hspan.symm ▸ hQ) (by simpa only [hnorm] using hsmall) (targetMonoid_norm_le_one η p) ha hρ
      halpha halpha1 heps heps1 hx hw hz (multiplicity p u.val) (multiplicity_lt_six u p hp)
    exact hb
  · rw [continuedCompensatedLocal_ramified η u P hs hP x w z]
    have hb := ramifiedSelected_central_quotient p hp hg.1 hg.2 _ _ _ x w z alpha eps
      (hspan.symm ▸ hQ) (by simpa only [hnorm] using hsmall) (targetMonoid_norm_le_one η p) ha hρ
      halpha halpha1 heps heps1 hx hw hz (multiplicity p u.val) (multiplicity_lt_six u p hp)
    dsimp only at hb
    simpa only [ramifiedCorrection,p,hnorm] using hb
end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source2249

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CentralSplit.lean; sha256: ad58dffec12b6f266030ae79073365ff6c5f6f12b75e7dd6f77170c6b8fb6862 -/
section Source2250
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

def centralNormalizedSlot (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  continuedCompensatedLocal η u P hs x w z
    (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
    supportedCorrection η u P x w z

def repeatedRowPrime (u : FreeRow) (P : PrimeIdeal) : Prop :=
  P.val∣Ideal.span {u.val} ∧ 2≤multiplicity (primaryGenerator P.val) u.val

def centralRegularError (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  if repeatedRowPrime u P then 0 else
    centralNormalizedSlot η u P hs x w z+star (idealRowHom u.val P.val)

def centralRepeatedTerm (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  if repeatedRowPrime u P then centralNormalizedSlot η u P hs x w z else 0

theorem centralNormalizedSlot_split (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    centralNormalizedSlot η u P hs x w z=
      -star (idealRowHom u.val P.val)+centralRegularError η u P hs x w z+
        centralRepeatedTerm η u P hs x w z := by
  by_cases hp : repeatedRowPrime u P
  · simp only [centralRegularError,centralRepeatedTerm,ite_eq_left hp,row_phase_ramified u P hp.1,
      star_zero,neg_zero,zero_add]
  · simp only [centralRegularError,centralRepeatedTerm,ite_eq_right hp]
    ring

theorem central_actual_local_bounds (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (480:ℝ)≤P.val.absNorm)
    (hsmall : 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖supportedCorrection η u P x w z‖ ∧
    ‖centralRegularError η u P hs x w z‖≤
      1440*(if P.val∣Ideal.span {u.val} then (P.val.absNorm:ℝ)^(1/2:ℝ)
        else (P.val.absNorm:ℝ)^(-(51/100:ℝ))) ∧
    ‖centralRepeatedTerm η u P hs x w z‖≤
      if repeatedRowPrime u P then 812*(P.val.absNorm:ℝ)^(1-w.re) else 0 := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQ1 : (1:ℝ)≤P.val.absNorm := by linarith
  by_cases hd : P.val∣Ideal.span {u.val}
  · have hb := actual_central_ramified_normalized η u P hs hd (by linarith)
      a e x w z hsmall ha ha1 he he1 hx hw hz
    have hcorr : supportedCorrection η u P x w z=ramifiedCorrection η u P hs x w z := by
      simp [supportedCorrection,hs,hd]
    refine ⟨hcorr.symm ▸ hb.1,?_,?_⟩
    · by_cases hj : 2≤multiplicity (primaryGenerator P.val) u.val
      · simp [centralRegularError,repeatedRowPrime,hd,hj]
        positivity
      · have hp : ¬repeatedRowPrime u P := fun h=>hj h.2
        rw [centralRegularError,ite_eq_right hp,row_phase_ramified u P hd,star_zero,add_zero,ite_eq_left hd]
        have h := hb.2
        simp only [ite_eq_right hj,add_zero] at h
        have hn : ‖centralNormalizedSlot η u P hs x w z‖≤800*(P.val.absNorm:ℝ)^(1/2:ℝ) := by
          dsimp only [centralNormalizedSlot]
          rw [hcorr]
          have hm := mul_le_mul_of_nonneg_left h hQ0.le
          have hpow : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-1:ℝ)=1 := by
            rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hQ0.ne'
          have hp2 : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-(1/2:ℝ))=
              (P.val.absNorm:ℝ)^(1/2:ℝ) := by
            conv_lhs => lhs;rw [←Real.rpow_one (P.val.absNorm:ℝ)]
            rw [←Real.rpow_add hQ0];norm_num
          rw [←mul_assoc,hpow,one_mul] at hm
          rw [mul_left_comm (P.val.absNorm:ℝ) 800,hp2] at hm
          exact hm
        exact hn.trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hQ0.le _))
    · by_cases hj : 2≤multiplicity (primaryGenerator P.val) u.val
      · have hp : repeatedRowPrime u P := ⟨hd,hj⟩
        rw [centralRepeatedTerm,ite_eq_left hp,ite_eq_left hp]
        have h := hb.2
        rw [ite_eq_left hj] at h
        have hpow : (P.val.absNorm:ℝ)^(-(1/2:ℝ))≤(P.val.absNorm:ℝ)^(-w.re) := by
          apply Real.rpow_le_rpow_of_exponent_le hQ1
          rw [hw];linarith
        have hn : (P.val.absNorm:ℝ)^(-1:ℝ)*‖centralNormalizedSlot η u P hs x w z‖≤
            812*(P.val.absNorm:ℝ)^(-w.re) := by
          dsimp only [centralNormalizedSlot];rw [hcorr]
          nlinarith
        have hm := mul_le_mul_of_nonneg_left hn hQ0.le
        have hi : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-1:ℝ)=1 := by
          rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hQ0.ne'
        have heq : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-w.re)=
            (P.val.absNorm:ℝ)^(1-w.re) := by
          conv_lhs => lhs;rw [←Real.rpow_one (P.val.absNorm:ℝ)]
          rw [←Real.rpow_add hQ0]; congr 1
        rw [←mul_assoc,hi,one_mul] at hm
        rw [mul_left_comm (P.val.absNorm:ℝ) 812,heq] at hm
        exact hm
      · have hp : ¬repeatedRowPrime u P := fun h=>hj h.2
        simp only [centralRepeatedTerm,ite_eq_right hp,norm_zero,le_refl]
  · have hb := actual_central_unramified_normalized η u P hs hd hη a e x w z hQ
      ha ha1 he he1 hx hw hz
    have hc : supportedCorrection η u P x w z=idealUnramifiedCorrection η u P x w z := by
      simp [supportedCorrection,hs,hd]
    have hp : ¬repeatedRowPrime u P := fun h=>hd h.1
    refine ⟨hc.symm ▸ hb.1,?_,?_⟩
    · simpa only [centralRegularError,ite_eq_right hp,centralNormalizedSlot,hc,ite_eq_right hd] using hb.2
    · simp only [centralRepeatedTerm,ite_eq_right hp,norm_zero,le_refl]
end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source2250

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CentralProduct.lean; sha256: c0213a7d86d447ddef6abf4c0f7eefc1cbc8aa7bb6b9f948cc6c4d63d675788b -/
section Source2251
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def centralRowScalar (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  (star ((calibrationForSet S hmax).residueMonoid u.val)*
    (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) w*
      HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x))*
    continuedCorrection S hS η u x w z

theorem calibratedTupleValue_central {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (a e : ℝ) (x w z : ℂ)
    (htail : FirstTail (4*e) S) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hx : x.re=a+16*e)
    (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hQ : ∀i,(480:ℝ)≤(P i).val.absNorm)
    (hη : ∀i,IsCoprime (P i).val η.modulus)
    (hsmall : ∀i,198*((P i).val.absNorm:ℝ)^(-10*e)≤1/2) :
    calibratedTupleValue S hS hmax η u P hPS W Y x w z=
      centralRowScalar S hS hmax η u x w z*
        ∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z := by
  have hrestore := continuedCorrection_restore (4*e) S hS htail (Finset.univ.image P)
    (tupleOutside S P hPS) η u x w z (by rw [hx];linarith) (by rw [hz])
    (by rw [hw];linarith) (by rw [hx,hw];linarith)
  rw [Finset.prod_image hP.injOn] at hrestore
  have hn : (∏i,supportedCorrection η u (P i) x w z)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _ hz0
    have h := (central_actual_local_bounds η u (P i)
      (outside_prime_supported S hS.bad (P i) (hPS i)) (hη i) a e x w z
      (hQ i) (hsmall i) ha ha1 he he1 hx hw hz).1
    rw [hz0,norm_zero] at h
    norm_num at h
  rw [calibratedTupleValue_factor S hS hmax η u P hP hPS W Y x w z]
  unfold centralRowScalar centralNormalizedSlot
  rw [hrestore]
  simp only [Finset.prod_mul_distrib,Finset.prod_div_distrib]
  field_simp

theorem calibrated_prime_slots_separate {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hPS : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (a e : ℝ) (x w z : ℂ)
    (htail : FirstTail (4*e) S) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hx : x.re=a+16*e)
    (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hQ : ∀i P,P∈T i→(480:ℝ)≤P.val.absNorm)
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hsmall : ∀i P,P∈T i→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) :
    (∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hPS i (P i).val (P i).property) W Y x w z)=
      centralRowScalar S hS hmax η u x w z*
        ∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u P.val
            (outside_prime_supported S hS.bad P.val (hPS i P.val P.property)) x w z := by
  calc
    _ = ∑P:(∀i,T i),centralRowScalar S hS hmax η u x w z*
        ∏i,W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u (P i).val
            (outside_prime_supported S hS.bad (P i).val (hPS i (P i).val (P i).property)) x w z := by
      apply Finset.sum_congr rfl
      intro P _
      exact calibratedTupleValue_central S hS hmax η u (fun i=>(P i).val) (hdis P)
        (fun i=>hPS i (P i).val (P i).property) W Y a e x w z htail ha ha1 he he1 hx hw hz
        (fun i=>hQ i (P i).val (P i).property) (fun i=>hη i (P i).val (P i).property)
        (fun i=>hsmall i (P i).val (P i).property)
    _ = _ := by
      rw [←Finset.mul_sum]
      congr 1
      exact (Fintype.prod_sum (fun i (P:T i)=>W i ((P.val.val.absNorm:ℝ)/Y i)*
        (P.val.val.absNorm:ℂ)^(z-1)*centralNormalizedSlot η u P.val
          (outside_prime_supported S hS.bad P.val (hPS i P.val P.property)) x w z)).symm

end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source2251

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CentralExpansion.lean; sha256: 5e5996b77a2787123e4fe5361f08b1a04843e9c615614f5e191ad6d700bc308e -/
section Source2252
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def centralBranch (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : Fin 3→ℂ :=
  ![-star (idealRowHom u.val P.val),centralRegularError η u P hs x w z,
    centralRepeatedTerm η u P hs x w z]

theorem central_branch_sum (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    centralNormalizedSlot η u P hs x w z=∑b:Fin 3,centralBranch η u P hs x w z b := by
  simpa [centralBranch,Fin.sum_univ_three] using centralNormalizedSlot_split η u P hs x w z

theorem central_slots_branch_expansion {K : ℕ}
    (η : Character) (u : FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    (∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralNormalizedSlot η u P.val (hT i P.val P.property) x w z)=
    ∑b:Fin K→Fin 3,∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralBranch η u P.val (hT i P.val P.property) x w z (b i) := by
  simp_rw [central_branch_sum,Finset.mul_sum]
  have hs (i : Fin K) :
      (∑P:T i,∑b:Fin 3,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralBranch η u P.val (hT i P.val P.property) x w z b)=
      ∑b:Fin 3,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralBranch η u P.val (hT i P.val P.property) x w z b := Finset.sum_comm
  simp_rw [hs]
  exact Fintype.prod_sum _

theorem calibrated_central_branch_expansion {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hPS : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (a e : ℝ) (x w z : ℂ)
    (htail : FirstTail (4*e) S) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hx : x.re=a+16*e)
    (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hQ : ∀i P,P∈T i→(480:ℝ)≤P.val.absNorm)
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hsmall : ∀i P,P∈T i→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) :
    (∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hPS i (P i).val (P i).property) W Y x w z)=
      centralRowScalar S hS hmax η u x w z*
      ∑b:Fin K→Fin 3,∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralBranch η u P.val
          (outside_prime_supported S hS.bad P.val (hPS i P.val P.property)) x w z (b i) := by
  rw [calibrated_prime_slots_separate S hS hmax η u T hPS hdis W Y a e x w z
    htail ha ha1 he he1 hx hw hz hQ hη hsmall]
  congr 1
  exact central_slots_branch_expansion η u T
    (fun i P hP=>outside_prime_supported S hS.bad P (hPS i P hP)) W Y x w z
end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source2252

/- Original source: OAI/NumberTheory/DirichletL/Detector/CentralBranchProduct.lean; sha256: 3020e59478bc1026778c48bccd6215b70b2a2099fa48a8c3a6b44253eb4a5dc3 -/
section Source2253
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralBranchProduct

theorem coupled_product_bound {ι : Type*} [Fintype ι]
    (L R : ℝ) (f g y : ι→ℝ) (hf : ∀i,0≤f i)
    (hsub : ∀J : Finset ι,L*(∏j ∈ J,g j)≤R*(∏j ∈ J,y j)) :
    L*(∏j : ι, (f j+g j))≤R*(∏j : ι, (f j+y j)) := by
  rw [Finset.prod_add,Finset.prod_add,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro J hJ
  calc
    _ = (∏j ∈ J,f j)*(L*∏j ∈ Finset.univ\J,g j) := by ring
    _ ≤ (∏j ∈ J,f j)*(R*∏j ∈ Finset.univ\J,y j) :=
      mul_le_mul_of_nonneg_left (hsub _) (Finset.prod_nonneg (fun j _=>hf j))
    _ = _ := by ring

theorem three_branch_bound {N : ℕ} (L R E : ℝ)
    (A B T : Fin N→ℂ) (y p : Fin N→ℝ)
    (hL : 0≤L) (hR : 0≤R) (hE : 0≤E) (hy : ∀j,0≤y j) (hp : ∀j,1≤p j)
    (hA : ∀j,‖A j‖≤y j*p j) (hB : ∀j,‖B j‖≤y j*E)
    (hT : ∀J : Finset (Fin N),L*(∏j ∈ J,‖T j‖)≤R*(∏j ∈ J,y j)) :
    L*‖∏j : Fin N, (A j+B j+T j)‖≤R*(E+2)^N*(∏j : Fin N, y j)*(∏j : Fin N,p j) := by
  have hnorm : ‖∏j : Fin N, (A j+B j+T j)‖≤∏j : Fin N,((‖A j‖+‖B j‖)+‖T j‖) := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro j _
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hc := coupled_product_bound L R (fun j=>‖A j‖+‖B j‖) (fun j=>‖T j‖) y
    (fun j=>add_nonneg (norm_nonneg _) (norm_nonneg _)) hT
  have hpoint (j : Fin N) : (‖A j‖+‖B j‖)+y j≤y j*((E+2)*p j) := by
    have h := hp j
    have hp0 : 0≤p j := zero_le_one.trans h
    have he := mul_nonneg (show 0≤E+1 by linarith) (show 0≤p j-1 by linarith)
    have hm := mul_nonneg (hy j) he
    nlinarith [hA j,hB j]
  calc
    _ ≤ L*(∏j : Fin N,((‖A j‖+‖B j‖)+‖T j‖)) := mul_le_mul_of_nonneg_left hnorm hL
    _ ≤ R*(∏j : Fin N,((‖A j‖+‖B j‖)+y j)) := hc
    _ ≤ R*(∏j : Fin N, y j*((E+2)*p j)) := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.prod_le_prod₀ (fun j _=>add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (hy j)) (fun j _=>hpoint j)
    _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin];ring
end SevenEighths.ProbeCentralBranchProduct

end

end OAI

end Source2253

/- Original source: OAI/NumberTheory/DirichletL/Detector/RowRadicalConductor.lean; sha256: 410a50259ddcb26cd84c20045a67bafedd227ec94c04441e6faebee92902372b -/
section Source2254
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeRowRadicalConductor
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem canonicalPrimePower_descent (P : Ideal O) [P.IsMaximal]
    (hg : λ₀ ∉ P) {c : ℕ} (hc : 1 ≤ c) (x : O ⧸ P ^ c) :
    CenteredMomentCanonical.canonicalPrimePowerCharacter P hg hc x =
      (CompletedGauss.actualSextic P hg ^ c)
        (CenteredMomentCorrelation.primePowerReduction P hc x) := rfl

theorem idealRowHom_congr_radical (I : Ideal O) (x y : O)
    (hxy : x-y ∈ I.radical) : idealRowHom x I = idealRowHom y I := by
  by_cases hI : I = 0
  · subst I
    simp only [map_zero]
  change (if I=0 then 0 else _) = (if I=0 then 0 else _)
  rw [ite_eq_right hI, ite_eq_right hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  have hp := Ideal.isPrime_of_prime (prime_of_normalized_factor P hP)
  have hle : I.radical ≤ P := hp.radical_le_iff.mpr
    (((Ideal.mem_normalizedFactors_iff hI).mp hP).2)
  unfold localRowValue
  split_ifs with hg
  · let : P.IsMaximal := hg.1
    congr 1
    exact Ideal.Quotient.eq.mpr (hle hxy)
  · rfl

theorem radical_ne_bot (I : Ideal O) (hI : I ≠ ⊥) : I.radical ≠ ⊥ := by
  intro h
  exact hI (bot_unique (h ▸ I.le_radical))

theorem movingNumeratorRow_radical_periodic (r : O)
    (hr : Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {r}).radical
      (movingNumeratorRow r hr) := idealRowHom_congr_radical _

theorem actualPeriodicRow_radical_periodic (Ψ : O →* ℂ) (Q : Ideal O)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (m : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo
      (Q * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical)
      (actualPeriodicRow Ψ m u a b r hr) := by
  intro x y hxy
  have hQ : x-y ∈ Q := Ideal.mul_le_left (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hm : x-y ∈ Ideal.span {m} := Ideal.mul_le_right (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have h72 : x-y ∈ Ideal.span {(72 : O)} := Ideal.mul_le_right (Ideal.mul_le_left hxy)
  have hrxy : x-y ∈ (Ideal.span {r}).radical := Ideal.mul_le_right hxy
  change ((Ψ x * coprimalityMask m x) * numeratorBadTwist u a b r hr x) *
      movingNumeratorRow r hr x =
    ((Ψ y * coprimalityMask m y) * numeratorBadTwist u a b r hr y) *
      movingNumeratorRow r hr y
  rw [hΨ x y hQ, coprimalityMask_periodic m x y hm,
    numeratorBadTwist_periodic u a b r hr x y h72,
    movingNumeratorRow_radical_periodic r hr x y hrxy]

theorem rowTwist_radical_periodic (η : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r-1) (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r) :
    CanonicalCoefficientClass.FactorsModulo
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical)
      (rowTwist (elementHom η) m f z) := by
  refine periodic_of_primary _ ?_ _ (actualPeriodicRow (elementHom η) m u a b r hr)
    (actualPeriodicRow_radical_periodic _ _ (elementHom_periodic η) _ _ _ _ _ hr)
    (rowTwist_unit_mul η m f z) ?_ ?_
  · have hd3 : λ₀ ^ 2 ∣ (3 : O) := ActualEisensteinCubic.lambda_sq_dvd_three
    have hd72 : λ₀ ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hd72))
  · intro n hn
    apply rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2
    intro hs
    exact ((supported_span_iff n).mp hs).1 hn
  · exact rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx

theorem rowTwist_nonzero_radical_unit (η : Character) (m f z n : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r)
    (hn : rowTwist (elementHom η) m f z n ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical) n) := by
  have hu := rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx hn
  have hle : η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r} ≤
      η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical :=
    Ideal.mul_mono_right (Ideal.span {r}).le_radical
  exact hu.map (Ideal.Quotient.factor hle)

theorem exists_row_character_radical (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character,
      χ.modulus.absNorm ≤ η.modulus.absNorm * (Ideal.span {m}).absNorm *
        (Ideal.span {(72 : O)}).absNorm * (Ideal.span {f^4*z}).radical.absNorm ∧
      ∀ n : O, elementCoeff χ n = rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, _, _, _, _⟩ :=
    exists_actual_periodic_row (elementHom η) η.modulus η.modulus_ne_bot
      (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  change f^4*z = (u : O)*λ₀^a*(2 : O)^b*r at hx
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical
  have hM : M ≠ ⊥ := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot
      (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    (radical_ne_bot _ hr.1)
  have hG := rowTwist_radical_periodic η m f z hmLam hm2 u a b r hr hpr hx
  refine ⟨HeckeRowClosure.rowCharacter M hM _ hG (rowTwist_unit η m f z), ?_, ?_⟩
  · change M.absNorm ≤ _
    have hfr : Ideal.span {f^4*z} ≤ (Ideal.span {r} : Ideal O) := by
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact Ideal.mem_span_singleton.mpr ⟨(u : O)*λ₀^a*(2 : O)^b, by rw [hx]; ring⟩
    have hF : (Ideal.span {f^4*z} : Ideal O).radical ≠ ⊥ :=
      radical_ne_bot _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (pow_ne_zero _ hf) hz))
    let : Finite (O ⧸ (Ideal.span {f^4*z} : Ideal O).radical) :=
      Ring.HasFiniteQuotients.finiteQuotient hF
    have hn := FiniteConductor.absNorm_le_of_le (Ideal.radical_mono hfr)
    simpa only [M, map_mul] using Nat.mul_le_mul_left
      (η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm) hn
  · intro n
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · exact Eq.symm (not_not.mp (fun h => hn
        (rowTwist_nonzero_radical_unit η m f z n hmLam hm2 u a b r hx h)))

theorem periodic_sup (G : O →* ℂ) (I J : Ideal O)
    (hI : CanonicalCoefficientClass.FactorsModulo I G)
    (hJ : CanonicalCoefficientClass.FactorsModulo J G) :
    CanonicalCoefficientClass.FactorsModulo (I ⊔ J) G := by
  intro x y hxy
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxy
  calc
    G x = G (x-a) := hI _ _ (by convert ha using 1; ring)
    _ = G y := hJ _ _ (by convert hb using 1; linear_combination -hab)

theorem primitive_of_equal_elements (χ θ : Character)
    (hel : ∀ n : O, elementCoeff χ n = elementCoeff θ n) :
    ∃ ψ : Character, χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ θ.modulus.absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  have hθ : CanonicalCoefficientClass.FactorsModulo θ.modulus (elementHom χ) := by
    intro x y hxy
    change elementCoeff χ x = elementCoeff χ y
    rw [hel x, hel y]
    exact elementHom_periodic θ x y hxy
  let M := χ.modulus ⊔ θ.modulus
  have hM : M ≠ ⊥ := fun h => χ.modulus_ne_bot (bot_unique (h ▸ le_sup_left))
  have hG := periodic_sup (elementHom χ) χ.modulus θ.modulus (elementHom_periodic χ) hθ
  have hu : ∀ u : Oˣ, elementHom χ (u : O) = 1 := fun u => χ.unit_trivial u
  let ρ := HeckeRowClosure.rowCharacter M hM (elementHom χ) hG hu
  have hr (n : O) : elementCoeff ρ n = elementCoeff χ n := by
    change elementCoeff (HeckeRowClosure.rowCharacter M hM _ hG hu) n = _
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · have hz : elementCoeff χ n = 0 := by
        by_contra hne
        have hu : IsUnit (Ideal.Quotient.mk χ.modulus n) := MulChar.apply_ne_zero_iff.mp hne
        exact hn (hu.map (Ideal.Quotient.factor (show χ.modulus ≤ M from le_sup_left)))
      exact hz.symm
  obtain ⟨ψ, hψ, hp, hn, hmask⟩ := exists_primitive_character ρ
  refine ⟨ψ, le_sup_left.trans hψ, hp, ?_, ?_⟩
  · let : Finite (O ⧸ θ.modulus) := Ring.HasFiniteQuotients.finiteQuotient θ.modulus_ne_bot
    exact hn.trans (FiniteConductor.absNorm_le_of_le (show θ.modulus ≤ M from le_sup_right))
  · intro I
    by_cases hI : I = 0
    · subst I
      simp only [map_zero, ite_self]
    let n := ConcretePrimeRowBridge.idealGenerator I
    have hn0 : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
    have hs : Ideal.span {n} = I := ConcretePrimeRowBridge.span_idealGenerator I
    have hre : idealCoeff ρ I = idealCoeff χ I := by
      rw [← hs, idealCoeff_span _ hn0, idealCoeff_span _ hn0, hr]
    by_cases hc : IsCoprime I χ.modulus
    · have hu : IsUnit (Ideal.Quotient.mk χ.modulus n) :=
        (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr (hs.symm ▸ hc)
      have huM : IsUnit (Ideal.Quotient.mk M n) :=
        hu.map (Ideal.Quotient.factor (show χ.modulus ≤ M from le_sup_left))
      have hcM : IsCoprime I M := hs ▸ (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp huM
      simpa only [hre, show ρ.modulus = M from rfl, hcM, hc, ite_true] using hmask I
    · rw [ite_eq_right hc]
      simpa only [hc, ite_false] using idealCoeff_source_mask χ I

theorem rawRow_small_presentation (u : HeckeInverseAmplification.FreeRow) :
    ∃ θ : Character,
      θ.modulus.absNorm ≤ ProbeHighRowFamily.conductorConstant *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ n : O, elementCoeff (ProbeHighRowFamily.rawRow u) n = elementCoeff θ n := by
  obtain ⟨θ, hn, he⟩ := exists_row_character_radical
    (ProbePhysical.fixedSourcePrincipal ∅ (by simp)) ProbeHighRowFamily.rowMaskElement 1 u.val
    ProbeHighRowFamily.rowMaskElement_ne_zero one_ne_zero u.property.1
    (dvd_mul_left _ _) (dvd_mul_right _ _)
  refine ⟨θ, ?_, ?_⟩
  · simpa [ProbeHighRowFamily.conductorConstant, ProbePhysical.fixedSourcePrincipal,
      HeckeRayFamily.character, Character.ofResidue] using hn
  · intro n
    have ho := (Classical.choose_spec
      (exists_row_character_with_conductor (ProbePhysical.fixedSourcePrincipal ∅ (by simp))
        ProbeHighRowFamily.rowMaskElement 1 u.val ProbeHighRowFamily.rowMaskElement_ne_zero
        one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2 n
    exact ho.trans (he n).symm

theorem rawRow_primitive_radical (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rawRow u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ ProbeHighRowFamily.conductorConstant *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rawRow u) I =
        if IsCoprime I (ProbeHighRowFamily.rawRow u).modulus then idealCoeff ψ I else 0 := by
  obtain ⟨θ, hn, he⟩ := rawRow_small_presentation u
  obtain ⟨ψ, hle, hp, hb, hmask⟩ := primitive_of_equal_elements _ θ he
  exact ⟨ψ, hle, hp, hb.trans hn, hmask⟩

theorem equal_elements_excludePrimes (χ θ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff θ n)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (n : O) :
    elementCoeff (χ.excludePrimes S hS) n = elementCoeff (θ.excludePrimes S hS) n := by
  have hc : IsCoprime (Ideal.span {n}) χ.modulus ↔ IsCoprime (Ideal.span {n}) θ.modulus := by
    have huχ : elementCoeff χ n ≠ 0 ↔ IsCoprime (Ideal.span {n}) χ.modulus :=
      MulChar.apply_ne_zero_iff.trans (IdealCharacter.isUnit_mk_iff_isCoprime _ _)
    have huθ : elementCoeff θ n ≠ 0 ↔ IsCoprime (Ideal.span {n}) θ.modulus :=
      MulChar.apply_ne_zero_iff.trans (IdealCharacter.isUnit_mk_iff_isCoprime _ _)
    rw [he n] at huχ
    exact huχ.symm.trans huθ
  simp only [Character.excludePrimes, elementCoeff_refineModulus,
    IdealCharacter.isUnit_mk_iff_isCoprime, IsCoprime.mul_right_iff, hc, he n]

def fixedConductorConstant (S : Finset (Ideal O)) : ℕ :=
  ProbeHighRowFamily.conductorConstant * (∏ P ∈ S, P).absNorm

theorem rowCharacter_primitive_radical (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0 := by
  obtain ⟨θ, hn, he⟩ := rawRow_small_presentation u
  obtain ⟨ψ, hle, hp, hb, hmask⟩ := primitive_of_equal_elements
    (ProbeHighRowFamily.rowCharacter S hS u) (θ.excludePrimes S hS)
    (equal_elements_excludePrimes _ θ he S hS)
  refine ⟨ψ, hle, hp, hb.trans ?_, hmask⟩
  change (θ.modulus * ∏ P ∈ S, P).absNorm ≤ _
  rw [map_mul]
  simpa only [fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm] using
    Nat.mul_le_mul_right ((∏ P ∈ S, P).absNorm) hn

theorem prod_le_radical_prod_pow {ι : Type*} (T : Finset ι)
    (P : ι → Ideal O) (e : ι → ℕ) (he : ∀ i ∈ T, 1 ≤ e i) :
    (∏ i ∈ T, P i) ≤ (∏ i ∈ T, P i ^ e i).radical := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hei : e i ≠ 0 := by have := he i (Finset.mem_insert_self i T); omega
    have hpow : (P i ^ e i).radical = (P i).radical := Ideal.radical_pow (P i) hei
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Ideal.radical_mul, hpow]
    exact Ideal.mul_le_inf.trans (inf_le_inf (P i).le_radical
      (ih (fun j hj => he j (Finset.mem_insert_of_mem hj))))

theorem radical_norm_selected_deficit {ι : Type*} [Fintype ι]
    (I : Ideal O) (hI : I ≠ 0) (P : ι → Ideal O)
    (hP : ∀ i, Prime (P i)) (hdis : Function.Injective P)
    (e : ι → ℕ) (he : ∀ i, 1 ≤ e i) (hdiv : ∀ i, P i ^ e i ∣ I) :
    I.radical.absNorm * ∏ i, (P i).absNorm ^ (e i - 1) ≤ I.absNorm := by
  let (i : ι) : (P i).IsMaximal := (Ideal.isPrime_of_prime (hP i)).isMaximal (hP i).ne_zero
  have hcop : Pairwise (fun i j => IsCoprime (P i ^ e i) (P j ^ e j)) := by
    intro i j hij
    exact (Ideal.isCoprime_of_isMaximal (hdis.ne hij)).pow
  obtain ⟨B, hB⟩ := Fintype.prod_dvd_of_coprime hcop hdiv
  have hB0 : B ≠ 0 := by
    intro hz
    apply hI
    rw [hB, hz, mul_zero]
  have hsmall0 : (∏ i, P i) * B ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => (hP i).ne_zero)) hB0
  have hsmall : (∏ i, P i) * B ≤ I.radical := by
    rw [hB, Ideal.radical_mul]
    exact Ideal.mul_le_inf.trans (inf_le_inf
      (prod_le_radical_prod_pow Finset.univ P e (fun i _ => he i)) B.le_radical)
  let : Finite (O ⧸ (∏ i, P i) * B) := Ring.HasFiniteQuotients.finiteQuotient hsmall0
  have hn := FiniteConductor.absNorm_le_of_le hsmall
  have hprod : (∏ i, P i) * (∏ i, P i ^ (e i-1)) = ∏ i, P i ^ e i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_succ']
    congr 1
    exact Nat.sub_add_cancel (he i)
  calc
    I.radical.absNorm * ∏ i, (P i).absNorm ^ (e i-1) ≤
        ((∏ i, P i) * B).absNorm * (∏ i, P i ^ (e i-1)).absNorm := by
      simpa only [map_prod, map_pow] using Nat.mul_le_mul_right
        (∏ i, (P i).absNorm ^ (e i-1)) hn
    _ = I.absNorm := by
      rw [← map_mul]
      congr 1
      calc
        ((∏ i, P i) * B) * (∏ i, P i ^ (e i-1)) =
            ((∏ i, P i) * (∏ i, P i ^ (e i-1))) * B := by ring
        _ = I := by rw [hprod, ← hB]

theorem rowCharacter_primitive_selected_deficit (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (e : Fin k → ℕ), (∀ i, 2 ≤ e i) →
          (∀ i, P i ^ e i ∣ Ideal.span {u.val}) →
          ψ.modulus.absNorm * ∏ i, (P i).absNorm ^ (e i-1) ≤
            fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).absNorm := by
  obtain ⟨ψ, hle, hp, hn, hm⟩ := rowCharacter_primitive_radical S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis e he hdiv
  have hb := radical_norm_selected_deficit (Ideal.span {u.val})
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1) P hP hdis e
    (fun i => (by have := he i; omega)) hdiv
  calc
    _ ≤ (fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).radical.absNorm) *
        ∏ i, (P i).absNorm ^ (e i-1) := Nat.mul_le_mul_right _ hn
    _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left (fixedConductorConstant S) hb

theorem canonicalCRT_radical_congr {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) (x y : O)
    (hxy : x-y ∈ (∏ i, P i ^ e i).radical) :
    CenteredMomentCanonical.canonicalCRTCharacter P hg e he hcop
        (Ideal.Quotient.mk (∏ i, P i ^ e i) x) =
      CenteredMomentCanonical.canonicalCRTCharacter P hg e he hcop
        (Ideal.Quotient.mk (∏ i, P i ^ e i) y) := by
  rw [CenteredMomentCanonical.canonicalCRTCharacter_mk,
    CenteredMomentCanonical.canonicalCRTCharacter_mk]
  exact idealRowHom_congr_radical _ x y hxy

theorem fixedConductorConstant_pos (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) : 0 < fixedConductorConstant S := by
  have hnorm (I : Ideal O) (hI : I ≠ 0) : 0 < I.absNorm :=
    Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  unfold fixedConductorConstant ProbeHighRowFamily.conductorConstant
  exact mul_pos (mul_pos
    (hnorm _ (Ideal.span_singleton_eq_bot.not.mpr ProbeHighRowFamily.rowMaskElement_ne_zero))
    (hnorm _ (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))))
    (hnorm _ (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)))

theorem sourceRow_primitive_radical (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
    (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, ProbePhysical.highExclusion S hS I * idealRowHom u.val I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0 := by
  obtain ⟨ψ, hle, hp, hn, hm⟩ := rowCharacter_primitive_radical S hS u
  refine ⟨ψ, hle, hp, hn, ?_⟩
  intro I
  rw [← ProbeHighRowFamily.rowCharacter_coeff S hS hbad u I]
  exact hm I

theorem rowCharacter_primitive_selected_div (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (e : Fin k → ℕ), (∀ i, 2 ≤ e i) →
          (∀ i, P i ^ e i ∣ Ideal.span {u.val}) →
          (ψ.modulus.absNorm : ℝ) ≤
            ((fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm) /
              ∏ i, ((P i).absNorm : ℝ) ^ (e i-1) := by
  obtain ⟨ψ, hle, hp, hm, hb⟩ := rowCharacter_primitive_selected_deficit S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis e he hdiv
  have hpos : 0 < ∏ i, ((P i).absNorm : ℝ) ^ (e i-1) := by
    apply Finset.prod_pos
    intro i _
    apply pow_pos
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hP i).ne_zero)
  apply (le_div_iff₀ hpos).mpr
  exact_mod_cast hb k P hP hdis e he hdiv

end SevenEighths.ProbeRowRadicalConductor

end

end OAI

end Source2254

/- Original source: OAI/NumberTheory/DirichletL/Detector/RowReflectedAllocation.lean; sha256: 1b84fb630dd4a48c1a8c77043279dacafddf61b45470f6e3cc2f770840099ed5 -/
section Source2255
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ComplexConjugate
open Set Complex
namespace SevenEighths.ProbeRowReflectedAllocation
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeFiniteDeletion HeckeReciprocalGrowth HeckeDeletionBounds
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

lemma prod_rpow_nonneg {ι : Type*} (T : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ T, 0 ≤ q i) (A : ℝ) :
    (∏ i ∈ T, q i) ^ A = ∏ i ∈ T, (q i) ^ A := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      Real.mul_rpow (hq i (Finset.mem_insert_self i T))
        (Finset.prod_nonneg (fun j hj => hq j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hq j (Finset.mem_insert_of_mem hj))]

lemma selected_exponent_allocation {a e : ℝ} (ha : 51/100 ≤ a)
    (he : 0 < e) {j : ℕ} (hj : 2 ≤ j) :
    -(1-a-6*e) ≤ (j-1 : ℕ)*(a-1/2+6*e)-1/2 := by
  have hA : 0 ≤ a-1/2+6*e := by linarith
  have hj' : (1 : ℝ) ≤ (j-1 : ℕ) := by exact_mod_cast (show 1 ≤ j-1 by omega)
  nlinarith [mul_le_mul_of_nonneg_right hj' hA]

theorem allocation_of_deficit {k : ℕ} (q : Fin k → ℝ)
    (hq : ∀ i, 1 ≤ q i) (j : Fin k → ℕ) (hj : ∀ i, 2 ≤ j i)
    (N D a e : ℝ) (hN : 0 ≤ N) (ha : 51/100 ≤ a) (he : 0 < e)
    (hdef : N * ∏ i, q i ^ (j i-1) ≤ D) :
    N ^ (a-1/2+6*e) * ∏ i, q i ^ (-(1-a-6*e)) ≤
      D ^ (a-1/2+6*e) * ∏ i, q i ^ (-(1/2 : ℝ)) := by
  let A := a-1/2+6*e
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hq0 (i) : 0 ≤ q i := (by linarith [hq i])
  have hlocal (i) : q i ^ (-(1-a-6*e)) ≤
      (q i ^ (j i-1)) ^ A * q i ^ (-(1/2 : ℝ)) := by
    rw [← Real.rpow_natCast_mul (hq0 i), ← Real.rpow_add (by linarith [hq i])]
    apply Real.rpow_le_rpow_of_exponent_le (hq i)
    exact selected_exponent_allocation ha he (hj i)
  have hprod := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => Real.rpow_nonneg (hq0 i) _)
    (fun i _ => hlocal i)
  rw [Finset.prod_mul_distrib, ← prod_rpow_nonneg Finset.univ
    (fun i => q i ^ (j i-1)) (fun i _ => pow_nonneg (hq0 i) _) A] at hprod
  have hD0 : 0 ≤ ∏ i, q i ^ (j i-1) := Finset.prod_nonneg (fun i _ => pow_nonneg (hq0 i) _)
  calc
    _ ≤ N ^ A * ((∏ i, q i ^ (j i-1)) ^ A * ∏ i, q i ^ (-(1/2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hN _)
    _ = (N * ∏ i, q i ^ (j i-1)) ^ A * ∏ i, q i ^ (-(1/2 : ℝ)) := by
      rw [Real.mul_rpow hN hD0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (mul_nonneg hN hD0) hdef hA)
      (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hq0 i) _))

lemma prime_norm_ge_one (P : Ideal O) (hP : Prime P) : (1 : ℝ) ≤ P.absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)

lemma original_row_conductor_le (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ((rowCharacter S hS u).modulus.absNorm : ℝ) ≤
      (fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm := by
  exact_mod_cast (by simpa only [fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm]
    using rowCharacter_conductor S hS u)

lemma original_row_deletion_radical_le (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ≤
      (fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm :=
  by
    let χ := rowCharacter S hS u
    have hd : radical χ.modulus ∣ χ.modulus := by
      unfold radical SmoothMobiusCorrection.primeProduct
      rw [SmoothMobiusCorrection.prod_primeSet χ.modulus (fun J : Ideal O => J)]
      exact IdealMobiusDivisorSum.support_product_dvd χ.modulus_ne_bot (Finset.Subset.refl _)
    have hn : ((radical χ.modulus).absNorm : ℝ) ≤ χ.modulus.absNorm := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)) (map_dvd Ideal.absNorm hd)
    exact hn.trans (original_row_conductor_le S hS u)

theorem row_same_primitive_allocation (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ∃ ψ : Character, (rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (rowCharacter S hS u) I =
        if IsCoprime I (rowCharacter S hS u).modulus then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (j : Fin k → ℕ), (∀ i, 2 ≤ j i) →
          (∀ i, P i ^ j i ∣ Ideal.span {u.val}) →
          ∀ a e : ℝ, 51/100 ≤ a → 0 < e →
          (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
              ∏ i, ((P i).absNorm : ℝ) ^ (-(1-a-6*e)) ≤
            ((fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm) ^
              (a-1/2+6*e) * ∏ i, ((P i).absNorm : ℝ) ^ (-(1/2 : ℝ)) := by
  obtain ⟨ψ, hle, hp, hm, hdef⟩ := rowCharacter_primitive_selected_deficit S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis j hj hdiv a e ha he
  apply allocation_of_deficit _ (fun i => prime_norm_ge_one _ (hP i)) j hj
    _ _ a e (by positivity) ha he
  exact_mod_cast hdef k P hP hdis j hj hdiv

lemma actual_multiplicity_divisor (u : FreeRow) (p : O) (hp : Prime p) :
    (Ideal.span {p} : Ideal O) ^ multiplicity p u.val ∣ Ideal.span {u.val} ∧
      multiplicity p u.val < 6 := by
  refine ⟨⟨Ideal.span {unitPart u p hp}, ?_⟩, multiplicity_lt_six u p hp⟩
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  exact congrArg (fun x : O => (Ideal.span {x} : Ideal O)) (unitPart_spec u p hp).1

lemma actual_ideal_multiplicity (u : FreeRow) (P : Ideal O) (hP : Prime P) :
    P ^ multiplicity P (Ideal.span {u.val} : Ideal O) ∣ Ideal.span {u.val} ∧
      multiplicity P (Ideal.span {u.val} : Ideal O) < 6 := by
  refine ⟨pow_multiplicity_dvd _ _, ?_⟩
  rw [UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors hP.irreducible
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1), normalize_eq]
  exact u.property.2 P

theorem buffered_reflected_right_bound (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
      detectorMaximum χ (3*(i+1 : ℕ)*B) < a+2*e →
      ∀ (j : ι), (χ j).residue ≠ 1 →
      ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
      ‖LFunction (χ j) (1-conj w)‖ ≤
        C * (presentationComplexity (χ j) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨C, hC, hb⟩ := buffered_regular_control e ε he he' hε
  refine ⟨C, hC, ?_⟩
  intro ι _ χ B a i hB ha ha1 hmax j hχ w hw hwi
  have hwr : (1-conj w).re = a+6*e := by simp; linarith
  have hwm : (1-conj w).im = w.im := by simp
  have hz : 1-conj w ∈ Metric.closedBall ((2 : ℂ)+w.im*I) (2-a-6*e) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : 1-conj w-((2 : ℂ)+w.im*I) = ((a+6*e-2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp; linarith
      · simp
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have h := hb χ B a i hB ha ha1 hmax j w.im hwi (1-conj w) hz
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal _ hχ] at h
  have hH : 0 ≤ (3*i+2 : ℕ)*B := (abs_nonneg _).trans hwi
  have hc : presentationComplexity (χ j) w.im ≤
      presentationComplexity (χ j) ((3*i+2 : ℕ)*B) := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    rw [abs_of_nonneg hH]
    gcongr
  apply (le_trans (le_add_of_nonneg_right (norm_nonneg _)) h).trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by
    unfold presentationComplexity HeckeLogarithmic.complexity; positivity) hc hε.le) hC.le

theorem central_deletion_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ ψ : Character) (a e : ℝ),
      0 < e → 51/100 ≤ a → a ≤ 1 →
      ∀ w : ℂ, w.re = 1-a-6*e →
      ‖factors χ.modulus ψ w‖ * ‖(factors χ.modulus ψ (1-conj w))⁻¹‖ ≤
        C * ((radical χ.modulus).absNorm : ℝ) ^ (6*e+2*ε) := by
  obtain ⟨Cl, hCl, hl⟩ := factors_any_re_subpower_bound ε hε
  obtain ⟨Cr, hCr, hr⟩ := factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Cl*Cr, mul_pos hCl hCr, ?_⟩
  intro χ ψ a e he ha ha1 w hw
  have hR := HeckeDyadic.radical_norm_ge_one χ.modulus
  have hR0 : 0 < ((radical χ.modulus).absNorm : ℝ) := by linarith
  have hleft : ‖factors χ.modulus ψ w‖ ≤
      Cl * ((radical χ.modulus).absNorm : ℝ) ^ (6*e+ε) := by
    apply (hl χ.modulus ψ w).trans
    apply mul_le_mul_of_nonneg_left _ hCl.le
    apply Real.rpow_le_rpow_of_exponent_le hR
    have hm : max (-w.re) 0 ≤ 6*e := max_le (by rw [hw]; linarith) (by positivity)
    linarith
  have hright : ‖(factors χ.modulus ψ (1-conj w))⁻¹‖ ≤
      Cr * ((radical χ.modulus).absNorm : ℝ) ^ ε := by
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans
      (hr χ.modulus ψ (1-conj w) (by simp; linarith))
  calc
    _ ≤ (Cl * ((radical χ.modulus).absNorm : ℝ) ^ (6*e+ε)) *
        (Cr * ((radical χ.modulus).absNorm : ℝ) ^ ε) :=
      mul_le_mul hleft hright (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hR0]
      congr 2
      ring

theorem buffered_same_primitive_reflected (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
      detectorMaximum χ (3*(i+1 : ℕ)*B) < a+2*e →
      ∀ (j : ι) (ψ : Character), FiniteFourier.IsPrimitiveOnIdeals ψ.residue →
      (χ j).residue ≠ 1 →
      (∀ I : Ideal O, idealCoeff (χ j) I =
        if IsCoprime I (χ j).modulus then idealCoeff ψ I else 0) →
      ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
      ‖LFunction (χ j) w‖ ≤ C * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
        ((radical (χ j).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
        (3+(3*i+2 : ℕ)*B)^2 *
        (presentationComplexity (χ j) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨Cg, hCg, hg⟩ := HeckeDyadicReflection.original_reflected_bound
  obtain ⟨Cb, hCb, hb⟩ := buffered_reflected_right_bound e ε he he' hε
  obtain ⟨Cd, hCd, hd⟩ := central_deletion_bound ε hε
  refine ⟨Cg*Cb*Cd, by positivity, ?_⟩
  intro ι _ χ B a i hB ha ha1 hmax j ψ hp hχ hm w hw hwi
  have hr := hg (χ j) ψ hp hχ hm w (by rw [hw]; linarith) (by rw [hw]; linarith)
  have hexp : 1/2-w.re = a-1/2+6*e := by rw [hw]; ring
  rw [hexp] at hr
  have hright := hb χ B a i hB ha ha1 hmax j hχ w hw hwi
  have hdel := hd (χ j) ψ a e he ha ha1 w hw
  have hpc0 : 0 ≤ presentationComplexity (χ j) ((3*i+2 : ℕ)*B) := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity
  calc
    _ ≤ Cg * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) * (3+|w.im|)^2 *
        ‖LFunction (χ j) (1-conj w)‖ *
        (‖factors (χ j).modulus ψ w‖ * ‖(factors (χ j).modulus ψ (1-conj w))⁻¹‖) := hr
    _ ≤ Cg * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) * (3+(3*i+2 : ℕ)*B)^2 *
        (Cb * (presentationComplexity (χ j) ((3*i+2 : ℕ)*B)) ^ ε) *
        (Cd * ((radical (χ j).modulus).absNorm : ℝ) ^ (6*e+2*ε)) := by
      gcongr
    _ = _ := by ring

theorem source_calibrated_reflected_allocation (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
      (hmaxS : ∀ P ∈ S, P.IsMaximal)
      (_hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
      (u : FreeRow), u.val ≠ 1 →
      ∃ ψ : Character, (rowCharacter S hS u).modulus ≤ ψ.modulus ∧
        FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        (∀ I : Ideal O, idealCoeff (rowCharacter S hS u) I =
          if IsCoprime I (rowCharacter S hS u).modulus then idealCoeff ψ I else 0) ∧
        (((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val ≠ 0) →
          (rowCharacter S hS u).residue ≠ 1 ∧ ψ.residue ≠ 1) ∧
        ∀ {ι : Type*} [Fintype ι] (η : Character) (twists : ι → Character)
          (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
          detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1 : ℕ)*B) < a+2*e →
          ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ j, Prime (P j)) → Function.Injective P →
          ∀ (v : Fin k → ℕ), (∀ j, 2 ≤ v j) →
            (∀ j, P j ^ v j ∣ Ideal.span {u.val}) →
            ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
            ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val) *
                HeckeOrigin.continued (rowCharacter S hS u) w‖ *
                ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) ≤
              C * (((fixedConductorConstant S : ℝ) *
                (Ideal.span {u.val} : Ideal O).absNorm) ^ (a-1/2+6*e) *
                ∏ j, ((P j).absNorm : ℝ) ^ (-(1/2 : ℝ))) *
                ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
                (3+(3*i+2 : ℕ)*B)^2 *
                (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨C, hC, hb⟩ := buffered_same_primitive_reflected e ε he he' hε
  refine ⟨C, hC, ?_⟩
  intro S hS hmaxS hbad u hu
  obtain ⟨ψ, hle, hp, hm, hall⟩ := row_same_primitive_allocation S hS u
  have hactive (hc : (ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val ≠ 0) :
      (rowCharacter S hS u).residue ≠ 1 ∧ ψ.residue ≠ 1 := by
    have hn := calibrated_row_nonprincipal S hS hmaxS hbad u hu hc
    exact ⟨hn, fun h => hn ((principal_iff_of_mask _ ψ hm).mpr h)⟩
  refine ⟨ψ, hle, hp, hm, hactive, ?_⟩
  intro ι _ η twists B a i hB ha ha1 hbin k P hP hdis v hv hdiv w hw hwi
  have hpc0 : 0 ≤ presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B) := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity
  by_cases hc : (ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val = 0
  · simp only [hc, star_zero, zero_mul, norm_zero]
    positivity
  · have hn := (hactive hc).1
    have hL := hb (sourceDetectorFamily S hS η u twists) B a i hB ha ha1 hbin
      (Sum.inl true) ψ hp hn hm w hw hwi
    simp only [sourceDetectorFamily_numerator] at hL
    have hcal : ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val)‖ ≤ 1 := by
      rw [norm_star]
      exact (ProbePhysical.calibrationForSet S hmaxS).residueMonoid_norm_le_one _
    have hweighted : ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val) *
        HeckeOrigin.continued (rowCharacter S hS u) w‖ ≤ ‖LFunction (rowCharacter S hS u) w‖ := by
      rw [HeckeOrigin.continued, ite_eq_right hn, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hcal
    have hal := hall k P hP hdis v hv hdiv a e ha he
    rw [← hw] at hal
    have hprod0 : 0 ≤ ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) :=
      Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (by positivity) _)
    calc
      _ ≤ (C * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
          ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
          (3+(3*i+2 : ℕ)*B)^2 *
          (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε) *
          ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) :=
        mul_le_mul_of_nonneg_right (hweighted.trans hL) hprod0
      _ = (C * ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
          (3+(3*i+2 : ℕ)*B)^2 *
          (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε) *
          ((ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
          ∏ j, ((P j).absNorm : ℝ) ^ (-w.re)) := by ring
      _ ≤ (C * ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
          (3+(3*i+2 : ℕ)*B)^2 *
          (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε) *
          ((((fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm) ^
            (a-1/2+6*e)) * ∏ j, ((P j).absNorm : ℝ) ^ (-(1/2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hal (by positivity)
      _ = _ := by ring

theorem source_actual_valuation_reflection (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
      (hmaxS : ∀ P ∈ S, P.IsMaximal)
      (_hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
      (u : FreeRow), u.val ≠ 1 →
      ∃ ψ : Character, (rowCharacter S hS u).modulus ≤ ψ.modulus ∧
        FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        (∀ I : Ideal O, idealCoeff (rowCharacter S hS u) I =
          if IsCoprime I (rowCharacter S hS u).modulus then idealCoeff ψ I else 0) ∧
        (((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val ≠ 0) →
          (rowCharacter S hS u).residue ≠ 1 ∧ ψ.residue ≠ 1) ∧
        ∀ {ι : Type*} [Fintype ι] (η : Character) (twists : ι → Character)
          (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
          detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1 : ℕ)*B) < a+2*e →
          ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ j, Prime (P j)) → Function.Injective P →
          (∀ j, 2 ≤ multiplicity (P j) (Ideal.span {u.val} : Ideal O)) →
          (∀ j, multiplicity (P j) (Ideal.span {u.val} : Ideal O) < 6) ∧
          ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
            ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val) *
                HeckeOrigin.continued (rowCharacter S hS u) w‖ *
                ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) ≤
              C * (((fixedConductorConstant S : ℝ) *
                (Ideal.span {u.val} : Ideal O).absNorm) ^ (a-1/2+6*e) *
                ∏ j, ((P j).absNorm : ℝ) ^ (-(1/2 : ℝ))) *
                ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
                (3+(3*i+2 : ℕ)*B)^2 *
                (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨C, hC, hb⟩ := source_calibrated_reflected_allocation e ε he he' hε
  refine ⟨C, hC, ?_⟩
  intro S hS hmaxS hbad u hu
  obtain ⟨ψ, hle, hp, hm, hactive, hbound⟩ := hb S hS hmaxS hbad u hu
  refine ⟨ψ, hle, hp, hm, hactive, ?_⟩
  intro ι _ η twists B a i hB ha ha1 hbin k P hP hdis hv
  refine ⟨fun j => (actual_ideal_multiplicity u (P j) (hP j)).2, ?_⟩
  exact hbound η twists B a i hB ha ha1 hbin k P hP hdis
    (fun j => multiplicity (P j) (Ideal.span {u.val} : Ideal O)) hv
    (fun j => (actual_ideal_multiplicity u (P j) (hP j)).1)

end SevenEighths.ProbeRowReflectedAllocation

end

end OAI

end Source2255

/- Original source: OAI/NumberTheory/DirichletL/Detector/CentralRepeatedProduct.lean; sha256: f39045d7916a6eafa0ede5783a30dd4a95de882a284dddfca261e01cd461997e -/
section Source2256
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedProduct
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CompletedGauss ProbeRowReflectedAllocation
open HeckeDeletionBounds HeckeReciprocalGrowth
local notation "O" => HeckeFamily.O

def rowCost (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (a e eps T : ℝ) : ℝ :=
  ((ProbeRowRadicalConductor.fixedConductorConstant S:ℝ)*(Ideal.span {u.val}:Ideal O).absNorm)^(a-1/2+6*e)*
    ((radical (rowCharacter S hS u).modulus).absNorm:ℝ)^(6*e+2*eps)*
    (3+T)^2*(presentationComplexity (rowCharacter S hS u) T)^eps

lemma rowCost_nonneg (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (a e eps T : ℝ) : 0≤rowCost S hS u a e eps T := by
  unfold rowCost presentationComplexity HeckeLogarithmic.complexity
  positivity

lemma repeated_weight_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (a e B Y : ℝ) (W : ℝ→ℂ) (x w z : ℂ)
    (hB : 0≤B) (hW : ∀t,‖W t‖≤B)
    (hQ : (480:ℝ)≤P.val.absNorm) (hsmall : 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hr : repeatedRowPrime u P) :
    ‖W ((P.val.absNorm:ℝ)/Y)*(P.val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u P hs x w z‖≤
      (812*B*(P.val.absNorm:ℝ)^z.re)*(P.val.absNorm:ℝ)^(-w.re) := by
  have hp : (0:ℝ)<P.val.absNorm := by linarith
  have hb := (central_actual_local_bounds η u P hs hη a e x w z hQ hsmall ha ha1 he he1 hx hw hz).2.2
  rw [ite_eq_left hr] at hb
  have hn : ‖(P.val.absNorm:ℂ)^(z-1)‖=(P.val.absNorm:ℝ)^(z.re-1) := by
    rw [show (P.val.absNorm:ℂ)=(((P.val.absNorm:ℝ):ℂ)) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp
  rw [norm_mul,norm_mul,hn]
  calc
    _ ≤ B*(P.val.absNorm:ℝ)^(z.re-1)*(812*(P.val.absNorm:ℝ)^(1-w.re)) := by
      gcongr
      exact hW _
    _ = _ := by
      calc
        _ = 812*B*((P.val.absNorm:ℝ)^(z.re-1)*(P.val.absNorm:ℝ)^(1-w.re)) := by ring
        _ = 812*B*(P.val.absNorm:ℝ)^(z.re-w.re) := by rw [←Real.rpow_add hp];congr 2;ring
        _ = _ := by rw [show z.re-w.re=z.re+(-w.re) by ring,Real.rpow_add hp];ring

theorem selected_repeated_product (e eps : ℝ) (he : 0<e) (he1 : e<1/1000)
    (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T a : ℝ) (i : ℕ),2<T → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T)<a+2*e →
    ∀(k : ℕ) (P : Fin k→PrimeIdeal) (hs : ∀j,Supported (P j).val),
      Function.Injective P → (∀j,IsCoprime (P j).val η.modulus) →
      (∀j,(480:ℝ)≤(P j).val.absNorm) →
      (∀j,198*((P j).val.absNorm:ℝ)^(-10*e)≤1/2) →
      (∀j,repeatedRowPrime u (P j)) →
    ∀(B : ℝ) (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),0≤B → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ∏j,‖W j (((P j).val.absNorm:ℝ)/Y j)*((P j).val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u (P j) (hs j) x w z‖ ≤
        C*(812*B)^k*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*
          ∏j,((P j).val.absNorm:ℝ)^(z.re-1/2) := by
  obtain ⟨C,hC,hbound⟩ := source_calibrated_reflected_allocation e eps he he1 heps
  refine ⟨C,hC,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T a i hT ha ha1 hbin k P hs hdis hη hQ hsmall hr B W Y hB hW x w z hx hw hz hwi
  obtain ⟨ψ,hle,hprim,hmask,hactive,hb⟩ := hbound S hS hmax hbad u hu
  have hi : Function.Injective (fun j=>(P j).val) := fun j l h=>hdis (Subtype.ext h)
  have hdiv (j : Fin k) := actual_multiplicity_divisor u (primaryGenerator (P j).val) (supported_primeGenerator_prime (P j) (hs j))
  have hspan (j : Fin k) : (Ideal.span {primaryGenerator (P j).val}:Ideal O)=(P j).val := span_primaryGenerator_of_supported (P j).val (hs j)
  have hb' := hb η twists T a i hT ha ha1 hbin k (fun j=>(P j).val) (fun j=>(P j).property) hi
    (fun j=>multiplicity (primaryGenerator (P j).val) u.val) (fun j=>(hr j).2)
    (fun j=>by have hd := (hdiv j).1;rw [hspan j] at hd;exact hd) w hw hwi
  let q : Fin k→ℝ := fun j=>(P j).val.absNorm
  have hq (j : Fin k) : 0<q j := by dsimp [q];have := hQ j;linarith
  have hp : (∏j,‖W j (q j/Y j)*((P j).val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u (P j) (hs j) x w z‖)≤
      (812*B)^k*(∏j,q j^z.re)*(∏j,q j^(-w.re)) := by
    have ht := Finset.prod_le_prod₀ (s:=Finset.univ) (fun j (_:j∈Finset.univ)=>norm_nonneg _)
      (fun j (_:j∈Finset.univ)=>repeated_weight_bound η u (P j) (hs j) (hη j)
        a e B (Y j) (W j) x w z hB (hW j) (hQ j) (hsmall j) ha ha1 he he1.le hx hw hz (hr j))
    simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow] using ht
  have hbc :
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ∏j,q j^(-w.re) ≤ C*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*∏j,q j^(-(1/2:ℝ)) := by
    convert hb' using 1 ; dsimp only [rowCost,q] ; ring
  have heq : (∏j,q j^z.re)*(∏j,q j^(-(1/2:ℝ)))=∏j,q j^(z.re-1/2) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [←Real.rpow_add (hq j)]
    congr 1
  calc
    _ ≤ ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ((812*B)^k*(∏j,q j^z.re)*(∏j,q j^(-w.re))) := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = ((812*B)^k*(∏j,q j^z.re))*(‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS u) w‖*∏j,q j^(-w.re)) := by ring
    _ ≤ ((812*B)^k*(∏j,q j^z.re))*(C*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*∏j,q j^(-(1/2:ℝ))) :=
      mul_le_mul_of_nonneg_left hbc (by positivity)
    _ = _ := by rw [show ((812*B)^k*(∏j,q j^z.re))*(C*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*∏j,q j^(-(1/2:ℝ)))=
      C*(812*B)^k*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*((∏j,q j^z.re)*(∏j,q j^(-(1/2:ℝ)))) by ring,heq]
end SevenEighths.ProbeCentralRepeatedProduct

end

end OAI

end Source2256

/- Original source: OAI/NumberTheory/DirichletL/Detector/CentralRepeatedChoices.lean; sha256: e57ad907c7377ac6e942f7faf1dceae374abd2dea2df39a1b05edd603c7452a9 -/
section Source2257
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedChoices
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
local notation "O" => HeckeFamily.O

def activeChoices {k : ℕ} (u : FreeRow) (T : Fin k→Finset PrimeIdeal)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) : Finset (∀j,T j) :=
  Finset.univ.filter (fun P=>∀j,repeatedRowPrime u (P j).val ∧
    W j (((P j).val.val.absNorm:ℝ)/Y j)≠0)

lemma active_card_le_divisors {k : ℕ} (u : FreeRow) (T : Fin k→Finset PrimeIdeal)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) :
    (activeChoices u T W Y).card≤(IdealMobiusDivisorSum.idealDivisors (Ideal.span {u.val})).card^k := by
  let U : Ideal O := Ideal.span {u.val}
  have hU : U≠0 := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  let f : activeChoices u T W Y→(Fin k→IdealMobiusDivisorSum.idealDivisors U) :=
    fun P j=>⟨(P.val j).val.val,(IdealMobiusDivisorSum.mem_idealDivisors hU).mpr
      (((Finset.mem_filter.mp P.property).2 j).1.1)⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    funext j
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun g=>(g j).val) h
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using hc

theorem active_card_subpower (N : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀k : ℕ,k≤N → ∀(u : FreeRow) (T : Fin k→Finset PrimeIdeal)
      (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),
      ((activeChoices u T W Y).card:ℝ)≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps := by
  let δ := eps/(N+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨(max 1 D)^N,by positivity,?_⟩
  intro k hk u T W Y
  have hU : (Ideal.span {u.val}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  have hU1 : (1:ℝ)≤(Ideal.span {u.val}:Ideal O).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU)
  have hd := hdiv (Ideal.span {u.val}) hU
  have hcard : ((activeChoices u T W Y).card:ℝ)≤
      ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {u.val})).card:ℝ)^k := by
    exact_mod_cast active_card_le_divisors u T W Y
  have hpow : D^k≤(max 1 D)^N :=
    (pow_le_pow_left₀ hD.le (le_max_right 1 D) k).trans (pow_le_pow_right₀ (le_max_left 1 D) hk)
  have hke : δ*k≤eps := by
    have hn : (k:ℝ)≤N := by exact_mod_cast hk
    have he : δ*(N+1)=eps := by dsimp [δ];field_simp
    nlinarith
  calc
    _ ≤ ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {u.val})).card:ℝ)^k := hcard
    _ ≤ (D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ)^k := pow_le_pow_left₀ (by positivity) hd k
    _ = D^k*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(δ*k) := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
    _ ≤ _ := mul_le_mul hpow (Real.rpow_le_rpow_of_exponent_le hU1 hke)
      (by positivity) (by positivity)

lemma sum_products_restrict {k : ℕ} (η : Character) (u : FreeRow)
    (T : Fin k→Finset PrimeIdeal) (hT : ∀j P,P∈T j→CanonicalQuadraticSieve.Supported P.val)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) (x w z : ℂ) :
    (∏j,∑P:T j,‖W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hT j P.val P.property) x w z‖)=
    ∑P∈activeChoices u T W Y,∏j,‖W j (((P j).val.val.absNorm:ℝ)/Y j)*((P j).val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u (P j).val (hT j (P j).val (P j).property) x w z‖ := by
  rw [Fintype.prod_sum]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro P _ hp
  have hn : ¬∀j,repeatedRowPrime u (P j).val ∧ W j (((P j).val.val.absNorm:ℝ)/Y j)≠0 := by
    simpa only [activeChoices,Finset.mem_filter,Finset.mem_univ,true_and] using hp
  push Not at hn
  obtain ⟨j,hj⟩ := hn
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  by_cases hr : repeatedRowPrime u (P j).val
  · simp [hj hr]
  · simp [centralRepeatedTerm,hr]
end SevenEighths.ProbeCentralRepeatedChoices

end

end OAI

end Source2257

/- Original source: OAI/NumberTheory/DirichletL/Detector/CentralRepeatedSum.lean; sha256: 4ecd5c6ac202151f659fea564b5c0c4c681f7aa60c5f32f5537ce0b02b30c86a -/
section Source2258
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedSum
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralRepeatedProduct ProbeCentralRepeatedChoices
open ProbeSelectedPrimeSums
local notation "O" => HeckeFamily.O

theorem actual_repeated_sum (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(k : ℕ),k≤N → ∀(T : Fin k→Finset PrimeIdeal)
      (hs : ∀j P,P∈T j→Supported P.val),
      (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        (∏j,∑P:T j,‖W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u P.val (hs j P.val P.property) x w z‖) ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏j,(Y j)^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hprod⟩ := selected_repeated_product e eps he he1 heps
  obtain ⟨D,hD,hcount⟩ := active_card_subpower N eps heps
  let A := annularPower c d (-(4/25:ℝ))
  let E := (max 1 (812*B*A))^N
  have hA : 0≤A := annularPower_nonneg c d _ hc
  have hE : 0<E := by dsimp [E];positivity
  refine ⟨D*C*E,by positivity,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin k hk T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi
  let R := rowCost S hS u a e eps ((3*i+2:ℕ)*T0)
  let L := ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖
  have hR : 0≤R := rowCost_nonneg _ _ _ _ _ _ _
  have hY0 (j : Fin k) : 0<Y j := zero_lt_one.trans_le (hY j)
  have hYY : 0≤∏j,(Y j)^(-(4/25:ℝ)) := Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (hY0 j).le _)
  have hterm (P : ∀j,T j) (hP : P∈activeChoices u T W Y) :
      L*(∏j,‖W j (((P j).val.val.absNorm:ℝ)/Y j)*((P j).val.val.absNorm:ℂ)^(z-1)*
        centralRepeatedTerm η u (P j).val (hs j (P j).val (P j).property) x w z‖)≤
      C*E*R*∏j,(Y j)^(-(4/25:ℝ)) := by
    have hp := (Finset.mem_filter.mp hP).2
    have hb := hprod S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin k
      (fun j=>(P j).val) (fun j=>hs j (P j).val (P j).property) (hdis P)
      (fun j=>hη j (P j).val (P j).property) (fun j=>hQ j (P j).val (P j).property)
      (fun j=>hsmall j (P j).val (P j).property) (fun j=>(hp j).1)
      B W Y hB hW x w z hx hw hz hwi
    have hpow : (∏j,((P j).val.val.absNorm:ℝ)^(z.re-1/2))≤A^k*∏j,(Y j)^(-(4/25:ℝ)) := by
      have hh := Finset.prod_le_prod₀ (s:=Finset.univ) (fun j _=>Real.rpow_nonneg (show (0:ℝ)≤(P j).val.val.absNorm by positivity) (-(4/25:ℝ)))
        (fun j (_:j∈Finset.univ)=>annular_rpow c d (Y j) ((P j).val.val.absNorm:ℝ) (-(4/25:ℝ)) hc hd (hY0 j)
          ((le_div_iff₀ (hY0 j)).mp (hWS j (hp j).2).1)
          ((div_le_iff₀ (hY0 j)).mp (hWS j (hp j).2).2))
      norm_num only [hz,show (17/50:ℝ)-1/2=-(4/25:ℝ) by norm_num] at ⊢
      simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
    have hEbound : (812*B)^k*A^k≤E := by
      rw [←mul_pow]
      exact (pow_le_pow_left₀ (by positivity) (le_max_right 1 (812*B*A)) k).trans
        (pow_le_pow_right₀ (le_max_left 1 _) hk)
    calc
      _ ≤ C*(812*B)^k*R*∏j,((P j).val.val.absNorm:ℝ)^(z.re-1/2) := hb
      _ ≤ C*(812*B)^k*R*(A^k*∏j,(Y j)^(-(4/25:ℝ))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = C*((812*B)^k*A^k)*R*∏j,(Y j)^(-(4/25:ℝ)) := by ring
      _ ≤ _ := by gcongr
  rw [sum_products_restrict η u T hs W Y x w z,Finset.mul_sum]
  have hh := Finset.sum_le_sum hterm
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  apply hh.trans
  calc
    _ ≤ (D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps)*(C*E*R*∏j,(Y j)^(-(4/25:ℝ))) :=
      mul_le_mul_of_nonneg_right (hcount k hk u T W Y) (by positivity)
    _ = _ := by dsimp [R];ring
end SevenEighths.ProbeCentralRepeatedSum

end

end OAI

end Source2258

/- Original source: OAI/NumberTheory/DirichletL/Detector/CentralRepeatedSubset.lean; sha256: 3c09b8f47efe4422099c9ae6beb0d032c8b3624a49f5e79008d70cabaaa7219c -/
section Source2259
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedSubset
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralRepeatedProduct ProbeCentralRepeatedSum
local notation "O" => HeckeFamily.O

theorem actual_repeated_subset (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset PrimeIdeal) (hs : ∀j P,P∈T j→Supported P.val),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀J : Finset (Fin N),
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        (∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖) ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏j:J,(Y j.val)^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hmain⟩ := actual_repeated_sum N e eps c d B he he1 heps hc hd hB
  refine ⟨C,hC,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi J
  let k := Fintype.card J
  let E : J≃Fin k := Fintype.equivFin J
  let idx : Fin k→Fin N := fun j=>(E.symm j).val
  have hi : Function.Injective idx := fun j l h=>E.symm.injective (Subtype.ext h)
  have hk : k≤N := by
    dsimp [k]
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using J.card_le_univ
  have hd' (P : ∀j,T (idx j)) : Function.Injective (fun j=>(P j).val) := by
    intro j l heq
    change (P j).val=(P l).val at heq
    by_contra hne
    have hdiff : idx j≠idx l := fun h=>hne (hi h)
    exact Finset.disjoint_left.mp (hdis _ _ hdiff) (P j).property (by rw [heq];exact (P l).property)
  have hb := hmain S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin k hk
    (fun j=>T (idx j)) (fun j P hP=>hs (idx j) P hP) hd'
    (fun j P hP=>hη (idx j) P hP) (fun j P hP=>hQ (idx j) P hP)
    (fun j P hP=>hsmall (idx j) P hP) (fun j=>W (idx j)) (fun j=>Y (idx j))
    (fun j=>hY (idx j)) (fun j=>hWS (idx j)) (fun j=>hW (idx j)) x w z hx hw hz hwi
  have hleft : (∏j:Fin k,∑P:T (idx j),‖W (idx j) ((P.val.val.absNorm:ℝ)/Y (idx j))*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hs (idx j) P.val P.property) x w z‖)=
      ∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖ :=
    Fintype.prod_equiv E.symm _ _ (fun _=>rfl)
  have hright : (∏j:Fin k,(Y (idx j))^(-(4/25:ℝ)))=∏j:J,(Y j.val)^(-(4/25:ℝ)) :=
    Fintype.prod_equiv E.symm _ _ (fun _=>rfl)
  rw [hleft,hright] at hb
  exact hb
end SevenEighths.ProbeCentralRepeatedSubset

end

end OAI

end Source2259

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CentralSlotSum.lean; sha256: c93e17cce027413068a5443715b78f516d3e27e0db4142ca30cb49508441289b -/
section Source2260
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem central_regular_slot_sum (eps c d B : ℝ) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (T : Finset PrimeIdeal)
      (hT : ∀P∈T,Supported P.val ∧ (480:ℝ)≤P.val.absNorm ∧ IsCoprime P.val η.modulus)
      (Y : ℝ),1≤Y → ∀(W : ℝ→ℂ),Function.support W⊆Set.Icc c d →
      (∀y,‖W y‖≤B) → ∀(a e : ℝ) (x w z : ℂ),
      (51/100:ℝ)≤a → a≤1 → 0<e → e≤1/1000 →
      x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 →
      (∀P∈T,198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
      (∑P:T,‖W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralRegularError η u P.val (hT P.val P.property).1 x w z‖)≤
      C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*Y^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed
    eps c d (-(4/25:ℝ)) 1 B 1440 heps hc hd (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro η u T hT Y hY W hWS hWB a e x w z ha ha1 he he1 hx hw hz hsmall
  let f : T→Ideal O := fun P=>P.val.val
  have hf : Function.Injective f := fun P Q h=>Subtype.ext (Subtype.ext h)
  let E : T→ℂ := fun P=>centralRegularError η u P.val (hT P.val P.property).1 x w z
  let G : T→ℂ := fun P=>((f P).absNorm:ℂ)^(1/2:ℂ)*E P
  have hnorm (P : T) : ‖G P‖≤1440*(if f P∣Ideal.span {u.val} then ((f P).absNorm:ℝ)^(1:ℝ) else 1) := by
    have hQ : (480:ℝ)≤(f P).absNorm := (hT P.val P.property).2.1
    have hQ0 : (0:ℝ)<(f P).absNorm := by linarith
    have hQ1 : (1:ℝ)≤(f P).absNorm := by linarith
    have hb := (central_actual_local_bounds η u P.val (hT P.val P.property).1
      (hT P.val P.property).2.2 a e x w z hQ (hsmall P.val P.property) ha ha1 he he1 hx hw hz).2.1
    have hn : ‖((f P).absNorm:ℂ)^(1/2:ℂ)‖=((f P).absNorm:ℝ)^(1/2:ℝ) := by
      rw [show ((f P).absNorm:ℂ)=(((f P).absNorm:ℝ):ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hQ0];norm_num
    dsimp only [G]
    rw [norm_mul,hn]
    calc
      _ ≤ ((f P).absNorm:ℝ)^(1/2:ℝ)*(1440*(if f P∣Ideal.span {u.val} then
          ((f P).absNorm:ℝ)^(1/2:ℝ) else ((f P).absNorm:ℝ)^(-(51/100:ℝ)))) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hQ0.le _)
      _ ≤ _ := by
        by_cases hp : f P∣Ideal.span {u.val}
        · simp only [ite_eq_left hp]
          rw [mul_left_comm,←Real.rpow_add hQ0]
          norm_num
        · simp only [ite_eq_right hp,mul_one]
          rw [mul_left_comm,←Real.rpow_add hQ0]
          have hh : ((f P).absNorm:ℝ)^((1/2:ℝ)-(51/100:ℝ))≤1 := by
            exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : (1/2:ℝ)-51/100≤0)).trans_eq (Real.rpow_zero _)
          norm_num only [show (1/2:ℝ)+-(51/100:ℝ)=(1/2:ℝ)-(51/100:ℝ) by ring]
          nlinarith
  have hb := hbound f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _=>P.val.property.ne_zero) W hWS hWB G (fun P _=>hnorm P)
    (z-1/2) (by simp only [Complex.sub_re];rw [hz];norm_num)
  have heq (P : T) :
      W (((f P).absNorm:ℝ)/Y)*((f P).absNorm:ℂ)^((z-1/2)-1)*G P=
      W (((f P).absNorm:ℝ)/Y)*((f P).absNorm:ℂ)^(z-1)*E P := by
    have hn : ((f P).absNorm:ℂ)≠0 := by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero
    dsimp only [G]
    rw [←mul_assoc,mul_assoc (W _) ,←Complex.cpow_add _ _ hn]
    rw [show (z - 1 / 2) - 1 + 1 / 2 = z - 1 by ring]
  simpa only [heq] using hb
end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source2260

/- Original source: OAI/NumberTheory/DirichletL/Detector/CentralAllSlots.lean; sha256: 44baeae06238618256fefe9973d1c120102a5451845dcbfcf3167570fd963231 -/
section Source2261
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralAllSlots
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ProbeCentralRepeatedProduct
open ProbeCentralRepeatedSubset ProbeCentralBranchProduct
local notation "O" => HeckeFamily.O

def phaseSlot (u : FreeRow) (T : Finset PrimeIdeal) (W : ℝ→ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  ∑P:T,W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*(-star (idealRowHom u.val P.val.val))

theorem actual_three_branch_slots (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset PrimeIdeal) (hs : ∀j P,P∈T j→Supported P.val),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀p : Fin N→ℝ,(∀j,1≤p j) → (∀j,‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j) →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ‖∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u P.val (hs j P.val P.property) x w z‖ ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by
  obtain ⟨Cr,hCr,hregular⟩ := central_regular_slot_sum eps c d B heps hc hd hB
  obtain ⟨Ct,hCt,hrepeated⟩ := actual_repeated_subset N e eps c d B he he1 heps hc hd hB
  refine ⟨Ct*(Cr+2)^N,by positivity,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi p hp hphase
  let L := ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖
  let U : ℝ := (Ideal.span {u.val}:Ideal O).absNorm
  let R := Ct*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*U^eps
  let A : Fin N→ℂ := fun j=>phaseSlot u (T j) (W j) (Y j) z
  let E : Fin N→ℂ := fun j=>∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
    centralRegularError η u P.val (hs j P.val P.property) x w z
  let F : Fin N→ℂ := fun j=>∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
    centralRepeatedTerm η u P.val (hs j P.val P.property) x w z
  let yy : Fin N→ℝ := fun j=>(Y j)^(-(4/25:ℝ))
  have hU : 1≤U := by dsimp [U];exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hUp : 1≤U^eps := Real.one_le_rpow hU heps.le
  have hR : 0≤R := by dsimp [R];exact mul_nonneg (mul_nonneg hCt.le (rowCost_nonneg _ _ _ _ _ _ _)) (Real.rpow_nonneg (zero_le_one.trans hU) _)
  have hyy (j : Fin N) : 0≤yy j := Real.rpow_nonneg (zero_le_one.trans (hY j)) _
  have hE (j : Fin N) : ‖E j‖≤yy j*(Cr*U^eps) := by
    have hb := hregular η u (T j) (fun P hP=>⟨hs j P hP,hQ j P hP,hη j P hP⟩)
      (Y j) (hY j) (W j) (hWS j) (hW j) a e x w z ha ha1 he he1.le hx hw hz (hsmall j)
    exact (norm_sum_le _ _).trans (hb.trans_eq (by dsimp [yy,U];ring))
  have hF (J : Finset (Fin N)) : L*(∏j∈J,‖F j‖)≤R*(∏j∈J,yy j) := by
    have hb := hrepeated S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall
      W Y hY hWS hW x w z hx hw hz hwi J
    have hp' : (∏j:J,‖F j.val‖)≤∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*
        (P.val.val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖ := by
      apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
      intro j _
      exact norm_sum_le _ _
    have hh := (mul_le_mul_of_nonneg_left hp' (show 0≤L from norm_nonneg _)).trans hb
    rw [Finset.prod_coe_sort J (fun j=>‖F j‖),
      Finset.prod_coe_sort J (fun j=>(Y j)^(-(4/25:ℝ)))] at hh
    exact hh
  have hb := three_branch_bound L R (Cr*U^eps) A E F yy p (norm_nonneg _) hR (by positivity) hyy hp hphase hE hF
  have heq : (∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralNormalizedSlot η u P.val (hs j P.val P.property) x w z)=∏j,(A j+E j+F j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [A,E,F,phaseSlot,centralNormalizedSlot_split,mul_add,Finset.sum_add_distrib]
  rw [heq]
  apply hb.trans
  have hcoef : (Cr*U^eps+2)^N≤(Cr+2)^N*U^(eps*N) := by
    have hh : Cr*U^eps+2≤(Cr+2)*U^eps := by nlinarith
    have hp' := pow_le_pow_left₀ (show 0≤Cr*U^eps+2 by positivity) hh N
    rw [mul_pow] at hp'
    have heq : (U^eps)^N=U^(eps*N) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hU)]
    rwa [heq] at hp'
  have hyprod : 0≤∏j,yy j := Finset.prod_nonneg (fun j _=>hyy j)
  have hpprod : 0≤∏j,p j := Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))
  calc
    _ ≤ R*((Cr+2)^N*U^(eps*N))*(∏j,yy j)*(∏j,p j) := by gcongr
    _ = _ := by
      dsimp [R,yy]
      have hh : U^eps*U^(eps*N)=U^(eps*(N+1)) := by rw [←Real.rpow_add (zero_lt_one.trans_le hU)];congr 1;ring
      calc
        _ = Ct*(Cr+2)^N*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*(U^eps*U^(eps*N))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by ring
        _ = _ := by rw [hh]
end SevenEighths.ProbeCentralAllSlots

end

end OAI

end Source2261

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CentralCosts.lean; sha256: 68864bda2cd363a8068ead715120d3ac2b02ff789fd8c1e183083d2535afaa1f -/
section Source2262
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical HeckeReciprocalGrowth
local notation "O" => HeckeFamily.O

def centralRemainingScalar (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x*
    continuedCorrection S hS η u x w z

lemma centralRowScalar_split (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow) (x w z : ℂ) :
    centralRowScalar S hS hmax η u x w z=
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      centralRemainingScalar S hS η u x w z := by
  unfold centralRowScalar centralRemainingScalar
  ring

theorem centralRemainingScalar_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : SourceExclusions S),FirstTail (4*e) S →
      ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖≤C*
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*
        (presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^eps := by
  obtain ⟨Ch,hCh,hh⟩ := continuedCorrection_first_subpower eps heps
  obtain ⟨Cr,hCr,hr⟩ := buffered_rectangle_reciprocal_bound e eps he he' heps
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨(L+1)*Cr*Ch,by positivity,?_⟩
  intro S hS hfirst η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L+1 :=
    (HeckeStripActual.LFunction_norm_le _ (by norm_num : (1:ℝ)<2)
      (by simp only [Complex.mul_re];rw [hz];norm_num)).trans (by linarith)
  have hc := hh (4*e) S hS hfirst η u x w z
    (by rw [hx];linarith) (by rw [hw];linarith) (by rw [hz]) (by rw [hx,hw];linarith)
  have hrec := hr (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
    (Sum.inl false) x (by rw [hx]) (by rw [hx];linarith) hxi
  simp only [sourceDetectorFamily_denominator] at hrec
  unfold centralRemainingScalar
  rw [norm_mul,norm_mul]
  apply (mul_le_mul (mul_le_mul hl hrec (norm_nonneg _) (by linarith)) hc (norm_nonneg _)
    (mul_nonneg (by linarith) (mul_nonneg hCr.le (Real.rpow_nonneg (by
      unfold presentationComplexity HeckeLogarithmic.complexity;positivity) _)))).trans
  exact le_of_eq (by ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2262

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CentralRowCost.lean; sha256: 5c145c60cf816384ba3eb73d9a1bc6eb9b943a90dba93c3028845268c2750f32 -/
section Source2263
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbeCentralRepeatedProduct
open ProbeRowReflectedAllocation ProbeRowRadicalConductor HeckeReciprocalGrowth HeckeDeletionBounds
local notation "O" => HeckeFamily.O

private lemma cost_power_identity (N L A R eps : ℝ) (hN : 0<N) (hL : 0<L) :
    N^A*N^R*L^2*(2*N^2*L^2)^eps=
      (2:ℝ)^eps*N^(A+R+2*eps)*L^(2+2*eps) := by
  have hp : (2*N^2*L^2)^eps=(2:ℝ)^eps*N^(2*eps)*L^(2*eps) := by
    rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by positivity) (by positivity)]
    rw [←Real.rpow_two N,←Real.rpow_two L,←Real.rpow_mul hN.le,←Real.rpow_mul hL.le]
  rw [hp]
  calc
    _ = (2:ℝ)^eps*(N^A*N^R*N^(2*eps))*(L^2*L^(2*eps)) := by ring
    _ = _ := by
      rw [←Real.rpow_add hN,←Real.rpow_add hN,←Real.rpow_two L,←Real.rpow_add hL]

theorem central_rowCost_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (e eps : ℝ) (he : 0<e) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀(u : FreeRow) (a H : ℝ),51/100≤a → a≤1 → 0≤H →
      rowCost S hS u a e eps H≤
        C*rowNorm u^(a-1/2+12*e+4*eps)*(3+H)^(2+2*eps) := by
  let F : ℝ := fixedConductorConstant S
  have hF : 1≤F := by
    dsimp [F]
    exact_mod_cast fixedConductorConstant_pos S hS
  have hFp : 0<F := zero_lt_one.trans_le hF
  refine ⟨(2:ℝ)^eps*F^(1/2+12*e+4*eps),by positivity,?_⟩
  intro u a H ha ha1 hH
  let N : ℝ := F*rowNorm u
  let L : ℝ := 3+H
  let A : ℝ := a-1/2+6*e
  let R : ℝ := 6*e+2*eps
  have hn : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hN : 0<N := mul_pos hFp hn
  have hL : 0<L := by dsimp [L];linarith
  have hA : 0≤A := by dsimp [A];linarith
  have hR : 0≤R := by dsimp [R];positivity
  have hrad : ((radical (rowCharacter S hS u).modulus).absNorm:ℝ)≤N :=
    original_row_deletion_radical_le S hS u
  have hq : ((rowCharacter S hS u).modulus.absNorm:ℝ)≤N := original_row_conductor_le S hS u
  have hc : presentationComplexity (rowCharacter S hS u) H≤2*N^2*L^2 := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    rw [abs_of_nonneg hH]
    calc
      _ ≤ N*(2*N*L^2) := by
        apply mul_le_mul hrad _ (by positivity) hN.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num)) (sq_nonneg L)
      _ = _ := by ring
  have hrpow := Real.rpow_le_rpow (show (0:ℝ)≤(radical (rowCharacter S hS u).modulus).absNorm by positivity) hrad hR
  have hcpow := Real.rpow_le_rpow (show 0≤presentationComplexity (rowCharacter S hS u) H by
    unfold presentationComplexity HeckeLogarithmic.complexity;positivity) hc heps.le
  have hbound : rowCost S hS u a e eps H≤N^A*N^R*L^2*(2*N^2*L^2)^eps := by
    unfold rowCost
    apply mul_le_mul _ hcpow (Real.rpow_nonneg (by
      unfold presentationComplexity HeckeLogarithmic.complexity;positivity) _) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg L)
    exact mul_le_mul_of_nonneg_left hrpow (Real.rpow_nonneg hN.le _)
  rw [cost_power_identity N L A R eps hN hL] at hbound
  have hexp : A+R+2*eps=a-1/2+12*e+4*eps := by dsimp [A,R];ring
  rw [hexp] at hbound
  apply hbound.trans
  dsimp only [N]
  rw [Real.mul_rpow hFp.le hn.le]
  have hf := Real.rpow_le_rpow_of_exponent_le hF
    (show a-1/2+12*e+4*eps≤1/2+12*e+4*eps by linarith)
  calc
    _ = ((2:ℝ)^eps*F^(a-1/2+12*e+4*eps))*rowNorm u^(a-1/2+12*e+4*eps)*L^(2+2*eps) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn.le _)
      exact mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg (by norm_num) _)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2263

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CentralTargetCost.lean; sha256: ae448d792907b09c9773ba9ec155558b36580f87ab8efb0daf33121f448dd845 -/
section Source2264
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical HeckeReciprocalGrowth HeckeDeletionBounds
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

lemma presentationComplexity_norm_bound (χ : Character) (H : ℝ) :
    presentationComplexity χ H≤2*(χ.modulus.absNorm:ℝ)^2*(3+|H|)^2 := by
  have hd : radical χ.modulus∣χ.modulus := by
    unfold radical SmoothMobiusCorrection.primeProduct
    rw [SmoothMobiusCorrection.prod_primeSet χ.modulus (fun J : Ideal O=>J)]
    exact IdealMobiusDivisorSum.support_product_dvd χ.modulus_ne_bot (Finset.Subset.refl _)
  have hn : ((radical χ.modulus).absNorm:ℝ)≤χ.modulus.absNorm := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)) (map_dvd Ideal.absNorm hd)
  unfold presentationComplexity HeckeLogarithmic.complexity
  calc
    _ ≤ (χ.modulus.absNorm:ℝ)*(2*χ.modulus.absNorm*(3+|H|)^2) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by ring

lemma target_complexity_norm_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (H : ℝ) (hH : 0≤H) :
    presentationComplexity ((targetRow η u).excludePrimes S hS) H≤
      2*((fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u)^2*(3+H)^2 := by
  have hn : (((targetRow η u).excludePrimes S hS).modulus.absNorm:ℝ)≤
      (fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u := by
    unfold rowNorm
    exact_mod_cast (by simpa only [fixedConductorConstant,mul_assoc,mul_comm,mul_left_comm] using
      targetRow_excluded_conductor S hS η u)
  apply (presentationComplexity_norm_bound _ H).trans
  rw [abs_of_nonneg hH]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (by positivity) (by unfold rowNorm;positivity)).mpr hn) (by norm_num)

lemma target_complexity_power_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (H eps : ℝ) (hH : 0≤H) (heps : 0≤eps) :
    (presentationComplexity ((targetRow η u).excludePrimes S hS) H)^eps≤
      (2*(fixedConductorConstant S:ℝ)^2)^eps*(η.modulus.absNorm:ℝ)^(2*eps)*
        rowNorm u^(2*eps)*(3+H)^(2*eps) := by
  have hb := Real.rpow_le_rpow (show 0≤presentationComplexity ((targetRow η u).excludePrimes S hS) H by
    unfold presentationComplexity HeckeLogarithmic.complexity;positivity)
    (target_complexity_norm_bound S hS η u H hH) heps
  apply hb.trans_eq
  rw [show 2*((fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u)^2*(3+H)^2=
    (2*(fixedConductorConstant S:ℝ)^2)*(η.modulus.absNorm:ℝ)^2*rowNorm u^2*(3+H)^2 by ring]
  rw [Real.mul_rpow (by unfold rowNorm;positivity) (by positivity),
    Real.mul_rpow (by positivity) (by unfold rowNorm;positivity),Real.mul_rpow (by positivity) (by positivity)]
  rw [←Real.rpow_two (η.modulus.absNorm:ℝ),←Real.rpow_two (rowNorm u),←Real.rpow_two (3+H),
    ←Real.rpow_mul (by positivity : (0:ℝ)≤η.modulus.absNorm),
    ←Real.rpow_mul (rowNorm_ge_one u |>.trans' (by norm_num : (0:ℝ)≤1)),
    ←Real.rpow_mul (by linarith : 0≤3+H)]

theorem centralRemainingScalar_arithmetic_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(3*eps)*(3+H)^(2*eps) := by
  obtain ⟨C,hC,hbound⟩ := centralRemainingScalar_bound e eps he he' heps
  have hF : 0<(fixedConductorConstant S:ℝ) := by exact_mod_cast fixedConductorConstant_pos S hS.prime
  refine ⟨C*(2*(fixedConductorConstant S:ℝ)^2)^eps,by positivity,?_⟩
  intro η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hh : 0≤H := (abs_nonneg _).trans hxi
  have hb := hbound S hS hfirst η u ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  apply hb.trans
  have hc := target_complexity_power_bound S hS.prime η u H eps hh heps.le
  have hn : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  calc
    _ ≤ C*rowNorm u^eps*((2*(fixedConductorConstant S:ℝ)^2)^eps*(η.modulus.absNorm:ℝ)^(2*eps)*
        rowNorm u^(2*eps)*(3+H)^(2*eps)) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by
      rw [show 3*eps=eps+2*eps by ring,Real.rpow_add hn]
      ring

theorem central_remaining_rowCost_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps H≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*(3+H)^(2+4*eps) := by
  obtain ⟨C0,hC0,h0⟩ := centralRemainingScalar_arithmetic_bound e eps he he' heps S hS hfirst
  obtain ⟨C1,hC1,h1⟩ := central_rowCost_bound S hS.prime e eps he heps
  refine ⟨C0*C1,mul_pos hC0 hC1,?_⟩
  intro η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hh : 0≤H := (abs_nonneg _).trans hxi
  have hn : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hL : 0<3+H := by linarith
  have h0' := h0 η u ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have h1' := h1 u a H ha ha1 hh
  apply (mul_le_mul h0' h1' (ProbeCentralRepeatedProduct.rowCost_nonneg S hS.prime u a e eps H)
    (by positivity)).trans_eq
  have hnp : rowNorm u^(3*eps)*rowNorm u^(a-1/2+12*e+4*eps)=
      rowNorm u^(a-1/2+12*e+7*eps) := by rw [←Real.rpow_add hn];congr 1;ring
  have hlp : (3+H)^(2*eps)*(3+H)^(2+2*eps)=(3+H)^(2+4*eps) := by
    rw [←Real.rpow_add hL];congr 1;ring
  calc
    _ = C0*C1*(η.modulus.absNorm:ℝ)^(2*eps)*
        (rowNorm u^(3*eps)*rowNorm u^(a-1/2+12*e+4*eps))*
        ((3+H)^(2*eps)*(3+H)^(2+2*eps)) := by ring
    _ = _ := by rw [hnp,hlp]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2264

/- Original source: OAI/NumberTheory/DirichletL/Detector/CentralPrimeSum.lean; sha256: 5a9d6aae268cee83f99c27c3339291a9a1fcb396128653ba5a2ec2857f34f40d -/
section Source2265
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralPrimeSum
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralAllSlots
local notation "O" => HeckeFamily.O

theorem actual_central_prime_sum (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset PrimeIdeal) (hPS : ∀j P,P∈T j→P.val∉S),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 →
      |x.im|≤(3*i+2:ℕ)*T0 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀p : Fin N→ℝ,(∀j,1≤p j) → (∀j,‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j) →
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
        (fun j=>hPS j (P j).val (P j).property) W Y x w z‖ ≤
      C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*
        (3+(3*i+2:ℕ)*T0)^(2+4*eps)*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by
  obtain ⟨Ca,hCa,hall⟩ := actual_three_branch_slots N e eps c d B he he1 heps hc hd hB
  obtain ⟨Cb,hCb,hcost⟩ := central_remaining_rowCost_bound e eps he he1 heps S hS hfirst
  refine ⟨Ca*Cb,mul_pos hCa hCb,?_⟩
  intro u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hPS hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hxi hwi p hp hphase
  let hs : ∀j P,P∈T j→Supported P.val := fun j P hP=>outside_prime_supported S hS.bad P (hPS j P hP)
  have hinj (P : ∀j,T j) : Function.Injective (fun j=>(P j).val) := by
    intro j l hh
    change (P j).val=(P l).val at hh
    by_contra hne
    exact Finset.disjoint_left.mp (hdis j l hne) (P j).property (by rw [hh];exact (P l).property)
  have ha' := hall S hS.prime hmax hS.bad u hu η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall
    W Y hY hWS hW x w z hx hw hz hwi p hp hphase
  have hc' := hcost η u twists T0 a ((3*i+2:ℕ)*T0) i hT0 ha ha1 le_rfl hbin x w z hx hw hz hxi
  have hN : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hy : 0≤∏j,(Y j)^(-(4/25:ℝ)) := Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (zero_le_one.trans (hY j)) _)
  have hpp : 0≤∏j,p j := Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))
  rw [calibrated_prime_slots_separate S hS hmax η u T hPS hinj W Y a e x w z
    hfirst ha ha1 he he1.le hx hw hz hQ hη hsmall,centralRowScalar_split,norm_mul,norm_mul]
  have hn := mul_le_mul_of_nonneg_left ha' (norm_nonneg (centralRemainingScalar S hS η u x w z))
  have hc'' := mul_le_mul_of_nonneg_right hc'
    (show 0≤Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) by positivity)
  have hpow : rowNorm u^(a-1/2+12*e+7*eps)*rowNorm u^(eps*(N+1))=
      rowNorm u^(a-1/2+12*e+eps*(N+8)) := by
    rw [←Real.rpow_add hN]
    congr 1
    ring
  calc
    _ = ‖centralRemainingScalar S hS η u x w z‖*
      (‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w‖*
        ‖∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*centralNormalizedSlot η u P.val (hs j P.val P.property) x w z‖) := by ring
    _ ≤ ‖centralRemainingScalar S hS η u x w z‖*
      (Ca*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*T0)*
        rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := hn
    _ = (‖centralRemainingScalar S hS η u x w z‖*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*T0))*
      (Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := by ring
    _ ≤ (Cb*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*(3+(3*i+2:ℕ)*T0)^(2+4*eps))*
      (Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := hc''
    _ = _ := by
      calc
        _ = Ca*Cb*(η.modulus.absNorm:ℝ)^(2*eps)*(rowNorm u^(a-1/2+12*e+7*eps)*rowNorm u^(eps*(N+1)))*
          (3+(3*i+2:ℕ)*T0)^(2+4*eps)*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by ring
        _ = _ := by rw [hpow]
end SevenEighths.ProbeCentralPrimeSum

end

end OAI

end Source2265

/- Original source: OAI/NumberTheory/DirichletL/Detector/RayPhaseBins.lean; sha256: e9d271f3a6302b5ed50e309b15d2fa670c6e6cccf553b9d815c56f204c3e4b54 -/
section Source2266
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeRayPhaseBins
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbeRayCharacterFamily
open HeckePrimeAmplitudeBins ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_phase_bins (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hAB : A≤B)
    (hWs : Function.support W⊆Ioo A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ cost mesh σmin σmax δ : ℝ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀(η : Character) (u : FreeRow),Z^δ≤rowNorm u →
      CanonicalQuadraticSieve.Supported (Ideal.span {u.val}) →
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^d →
    ∀(a : ℝ) (i : ℕ),51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u
        (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse)) (3*(i+1:ℕ)*Z^τ)<a+2*e →
    ∀(r : ℝ) (z : ℂ),rmin≤r → r≤R → σmin≤1-z.re → 1-z.re≤σmax →
      |z.im|+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^cost →
    let D := (Z^d)^r
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H u.val W B D z
    let g := amplitude D (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤D^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) ∧
      ‖∑P∈pool (RayQuotient.identityClass M H) S A B D,
        W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val))‖≤D^(z.re-1/2+g+mesh) := by
  have hb := HeckePrimeAmplitudeActual.ray_amplitude_bins M H hH W A B hA
    (hWs.trans Ioo_subset_Icc_self) hW R dmin dmax rmin τ ε e κ cost mesh σmin σmax
    hR hdmin hdmax hrmin hτ hε he he' hκ hcost hmesh hbudget hgap
  have hn := large_supported_twists_eventually M δ hδ
  have ht := ProbeRaySlots.power_fixed_exclusions S A (dmin*rmin) hA (mul_pos hdmin hrmin)
    (fun p : {p : ℝ×ℝ // dmin≤p.1 ∧ rmin≤p.2}=>p.val.1*p.val.2)
    (fun p=>mul_le_mul p.property.1 p.property.2 hrmin.le (hdmin.trans_le p.property.1).le)
  filter_upwards [hb,hn,ht,eventually_ge_atTop (1:ℝ)] with Z hb hn ht hZ
  intro d hd hd' hU hT η u hu hs hcond a i ha ha' hbin r z hr hr' hσ hσ' hf hh
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _
  have hsmall : ∀P∈S,(P.absNorm:ℝ)≤A*(Z^d)^r := by
    intro P hP
    rw [←Real.rpow_mul hZp.le]
    exact ht ⟨(d,r),hd,hr⟩ P hP
  have hnp := hn u hu hs H hH
  have hzmax := (source_nonprincipal_maximum_dominates S hS η u
    (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse) hnp _).trans_lt hbin
  have hq (θ : RayQuotient.Characters M H) :
      ((HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm:ℝ)≤Z^d :=
    (show ((HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm:ℝ)≤
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ) by
        exact_mod_cast raw_twisted_conductor M H hH u θ).trans hcond
  have heq := canonical_amplitude_raw M H S hS hbad u W A B ((Z^d)^r) hD hWs hsmall z
  have hbins := hb d hd hd' hU hT (rawRow u).inverse hnp a i ha ha' hzmax
    r (1-z.re) z.im hr hr' hσ hσ' hq hf hh
  rw [←heq] at hbins
  refine ⟨hbins.1,hbins.2.1,hbins.2.2.1,hbins.2.2.2.1,hbins.2.2.2.2,?_⟩
  rw [central_phase_norm M H S u.val W A B ((Z^d)^r) hA hAB hD hWs hsmall z]
  calc
    _ ≤ ((Z^d)^r)^(z.re-1/2)*((Z^d)^r)^(_+mesh) :=
      mul_le_mul_of_nonneg_left hbins.2.2.2.1 (Real.rpow_nonneg hD.le _)
    _ = _ := by rw [←Real.rpow_add hD];congr 1;ring
end SevenEighths.ProbeRayPhaseBins

end

end OAI

end Source2266

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CubeScale.lean; sha256: 8455534043a275bbc802b7e6f3f5435a833dfabd40d63c5ab66ea439503bdab2 -/
section Source2267
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem cube_height_budget_eventually (n : ℕ) (τ dmin cost : ℝ)
    (hτ : 0<τ) (hc : 0≤cost) (hgap : 2*τ<dmin*cost) :
    ∀ᶠ Z : ℝ in atTop,∀i : ℕ,i≤n → ∀d : ℝ,dmin≤d →
      (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^cost := by
  have habs := HeckeDyadic.constant_absorbed_eventually
    ((3*(n:ℝ)+5)^2) (dmin*cost-2*τ) (by linarith)
  filter_upwards [habs,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro i hi d hd
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hpow : 1≤Z^τ := Real.one_le_rpow hZ hτ.le
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  have hx : 3+(3*i+2:ℕ)*Z^τ≤(3*(n:ℝ)+5)*Z^τ := by
    push_cast
    nlinarith
  calc
    _ ≤ ((3*(n:ℝ)+5)*Z^τ)^2 := by
      apply sq_le_sq₀ (by positivity) (by positivity) |>.mpr hx
    _ = (3*(n:ℝ)+5)^2*Z^(2*τ) := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_two,←Real.rpow_mul hZp.le]
      congr 1
      ring
    _ ≤ Z^(dmin*cost-2*τ)*Z^(2*τ) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(dmin*cost) := by rw [←Real.rpow_add hZp];congr 1;ring
    _ ≤ (Z^d)^cost := by
      rw [←Real.rpow_mul hZp.le]
      exact Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd hc)

theorem ray_cube_conductor_eventually (M : Ideal O) (ν : ℝ) (hν : 0<ν) :
    ∀ᶠ Z : ℝ in atTop,∀(u : FreeRow) (d : ℝ),rowNorm u≤Z^(d-ν) →
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^d := by
  have hh := HeckeDyadic.constant_absorbed_eventually
    ((conductorConstant*M.absNorm:ℕ):ℝ) ν hν
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hC hZ
  intro u d hu
  calc
    _ = ((conductorConstant*M.absNorm:ℕ):ℝ)*rowNorm u := by simp [rowNorm]
    _ ≤ Z^ν*Z^(d-ν) := mul_le_mul hC hu (by unfold rowNorm;positivity) (Real.rpow_nonneg hZ.le _)
    _ = Z^d := by rw [←Real.rpow_add hZ];congr 1;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2267

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CubePhaseBins.lean; sha256: c09694944039cd83fefea60beb77ac553d3779cf9814d736f38d3963ddd413c0 -/
section Source2268
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbeRayCharacterFamily
open HeckePrimeAmplitudeBins ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_phase_bins_on_cube (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (hmax : ∀P∈S,P.IsMaximal)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hAB : A≤B)
    (hWs : Function.support W⊆Ioo A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ cost mesh δ ν : ℝ) (n : ℕ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hν : 0<ν) (hheight : 2*τ<dmin*cost) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀(η : Character) (u : FreeRow),Z^δ≤rowNorm u →
      (ProbePhysical.calibrationForSet S hmax).residueMonoid u.val≠0 →
      rowNorm u≤Z^(d-ν) →
    ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u
        (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse)) (3*(i+1:ℕ)*Z^τ)<a+2*e →
    ∀(r : ℝ) (t : ProbeMellinBoundary.HeightSpace),rmin≤r → r≤R →
      ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
    let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
    let D := (Z^d)^r
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H u.val W B D z
    let g := amplitude D (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤D^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) ∧
      ‖∑P∈pool (RayQuotient.identityClass M H) S A B D,
        W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val))‖≤D^(z.re-1/2+g+mesh) := by
  have hb := ProbeRayPhaseBins.actual_phase_bins M H hH S hS hbad W A B hA hAB hWs hW
    R dmin dmax rmin τ ε e κ cost mesh (33/50) (33/50) δ
    hR hdmin hdmax hrmin hτ hε he he' hκ hcost hmesh hδ hbudget hgap
  filter_upwards [hb,cube_height_budget_eventually n τ dmin cost hτ hcost hheight,
    ray_cube_conductor_eventually M ν hν,eventually_gt_atTop (0:ℝ)] with Z hb hh hc hZ
  intro d hd hd' hU hT η u hu hcal hrow a i hi ha ha' hbin r t hr hr' ht
  have hs := calibration_nonzero_supported S hmax hbad u.val hcal
  have hpow : 0≤Z^τ := Real.rpow_nonneg hZ.le _
  have hbuffer : ((3*i+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*i+2:ℕ)*Z^τ := by
    push_cast
    nlinarith
  have hfreq := (cube_buffered_heights t ((3*i+1:ℕ)*Z^τ) (Z^τ) i ht hpow hbuffer).2.2
  have hb' := hb d hd hd' hU hT η u hu hs (hc u d hrow) a i ha ha' hbin r
    ((17/50:ℂ)+t.1.2*Complex.I) hr hr'
    (by norm_num) (by norm_num) (by simpa using hfreq) (hh i hi d hd)
  exact hb'

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2268

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CubePrimeThresholds.lean; sha256: 19753c4d672e2a1b47029e850ec5f468f9a566c50bcf535022b723cf28640872 -/
section Source2269
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbeRaySlots
local notation "O" => HeckeFamily.O

theorem central_pool_good_eventually (η : Character) (e c b dmin rmin : ℝ)
    (he : 0<e) (hc : 0<c) (hcb : c≤b) (hd : 0<dmin) (hr : 0<rmin) :
    ∀ᶠ Z : ℝ in atTop,∀(C : Set (Ideal O)) (S : Finset (Ideal O)) (d r : ℝ),dmin≤d → rmin≤r →
      ∀P∈pool C S c b ((Z^d)^r),P.val∉S ∧ IsCoprime P.val η.modulus ∧
        (480:ℝ)≤P.val.absNorm ∧ 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2 := by
  obtain ⟨Q0,hQ0,hsmall⟩ := ProbeEuler.central_correction_threshold e he
  have ht := (tendsto_rpow_atTop (mul_pos hd hr)).const_mul_atTop hc
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop Q0),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ))] with Z hZ hQ hη
  intro C S d r hdd hrr P hP
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _
  have hle : c*Z^(dmin*rmin)≤c*(Z^d)^r := by
    rw [←Real.rpow_mul hZp.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ
      (mul_le_mul hdd hrr hr.le (hd.trans_le hdd).le)) hc.le
  have hl := (pool_norm_bounds C S hc.le hcb hD P hP).1
  have hq : Q0≤(P.val.absNorm:ℝ) := hQ.trans (hle.trans (by linarith))
  exact ⟨(mem_pool C S c b _ P).mp hP |>.2.2.2,
    prime_coprime_of_norm_gt η P (hη.trans_le (hle.trans (by linarith))),hQ0.trans hq,hsmall _ hq⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2269

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CentralHeightCost.lean; sha256: f707a9e752921c6a6fd7dfbb36a4b1edb1633ed90393cd7fe86f28fe9164f1c3 -/
section Source2270
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem cube_height_power_eventually (n : ℕ) (τ p loss : ℝ)
    (hτ : 0<τ) (hp : 0≤p) (hgap : τ*p<loss) :
    ∀ᶠ Z : ℝ in atTop,∀i : ℕ,i≤n → (3+(3*i+2:ℕ)*Z^τ)^p≤Z^loss := by
  have hh := HeckeDyadic.constant_absorbed_eventually ((3*(n:ℝ)+5)^p)
    (loss-τ*p) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro i hi
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hpow : 1≤Z^τ := Real.one_le_rpow hZ hτ.le
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  have hx : 3+(3*i+2:ℕ)*Z^τ≤(3*(n:ℝ)+5)*Z^τ := by push_cast;nlinarith
  calc
    _ ≤ ((3*(n:ℝ)+5)*Z^τ)^p := Real.rpow_le_rpow (by positivity) hx hp
    _ = (3*(n:ℝ)+5)^p*Z^(τ*p) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hZp.le _),←Real.rpow_mul hZp.le]
    _ ≤ Z^(loss-τ*p)*Z^(τ*p) := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^loss := by rw [←Real.rpow_add hZp];congr 1;ring

theorem central_remaining_rowCost_scale (e eps τ loss : ℝ) (n : ℕ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps) (hτ : 0<τ)
    (hgap : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,∀(η : Character) (u : FreeRow)
      {ι : Type*} [Fintype ι] (ψ : ι→Character) (a : ℝ) (i : ℕ),i≤n →
      51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*Z^τ)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤(3*i+2:ℕ)*Z^τ →
      ‖centralRemainingScalar S hS η u x w z‖*
        ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*Z^τ)≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*Z^loss := by
  obtain ⟨C,hC,hbound⟩ := central_remaining_rowCost_bound e eps he he' heps S hS hfirst
  refine ⟨C,hC,?_⟩
  filter_upwards [cube_height_power_eventually n τ (2+4*eps) loss hτ (by positivity) hgap,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))] with Z hheight hZ
  intro η u ι _ ψ a i hi ha ha1 hbin x w z hx hw hz hxi
  have hb := hbound η u ψ (Z^τ) a ((3*i+2:ℕ)*Z^τ) i hZ ha ha1 le_rfl hbin x w z hx hw hz hxi
  exact hb.trans (mul_le_mul_of_nonneg_left (hheight i hi) (by unfold rowNorm;positivity))

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2270

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CubePrimeBound.lean; sha256: e5608bd6e9fe2c79895cd36e7556b7bd34064d57f270eafefa76cc7f050318f5 -/
section Source2271
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots ProbeCentralAllSlots HeckePrimeAmplitudeBins
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem poolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_cube_prime_bound (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(u : FreeRow),u.val≠1 → Z^δ≤rowNorm u →
      (calibrationForSet S hmax).residueMonoid u.val≠0 → rowNorm u≤Z^(d-margin) →
      ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e →
      ∀r : Fin N→ℝ,(∀j,rmin≤r j) → (∀j,r j≤R) →
      let Y : Fin N→ℝ := fun j=>(Z^d)^(r j)
      let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let x : ℂ := (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I)
      let w : ℂ := (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      let Q : Fin N→ℂ := fun j=>HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z
      let g : Fin N→ℝ := fun j=>amplitude (Y j) (a-1/2) mesh (Q j)
      (∀j,0≤g j ∧ g j≤a-1/2 ∧ g j∈labels (a-1/2) mesh ∧
        ‖Q j‖≤(Y j)^(g j+mesh) ∧ (0<g j → (Z^d)^(2*r j*g j)≤‖Q j‖^2)) ∧
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=>poolOutside M H S N c b Y j (P j).val (P j).property) W Y x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*
          (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh)) := by
  have hb (j : Fin N) := actual_phase_bins_on_cube M H hH S hS.prime hS.bad hmax (W j) c b hc hcb
    (hWs j) (hW j) R dmin dmax rmin τ ε e κ cost mesh δ margin n
    hR hdmin hdmax hrmin hτ hε he he1 hκ hcost hmesh hδ hbudget hgap hmargin hheight
  have hbAll := Filter.eventually_all.mpr hb
  obtain ⟨C,hC,hbound⟩ := ProbeCentralPrimeSum.actual_central_prime_sum N e eps c b A
    he he1 heps hc (hc.trans_le hcb) hA S hS hfirst hmax
  refine ⟨C,hC,?_⟩
  intro η
  have hscale := HeckeDetectorDyadicGeometry.uniform_scale_threshold dmin 2 hdmin
  filter_upwards [hbAll,central_pool_good_eventually η e c b dmin rmin he hc hcb hdmin hrmin,
    cube_height_power_eventually n τ (2+4*eps) loss hτ (by positivity) hloss,
    hscale,source_cube_height_eventually τ hτ] with Z hb hg hheightZ hscaleZ hZ
  intro d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin r hr hr'
  dsimp only
  intro hdis t ht
  let Y : Fin N→ℝ := fun j=>(Z^d)^(r j)
  let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let g : Fin N→ℝ := fun j=>amplitude (Y j) (a-1/2) mesh
    (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
  have hU : 2≤Z^d := hscaleZ d hd
  have hUp : 0<Z^d := by linarith
  have hY (j : Fin N) : 1≤Y j := Real.one_le_rpow (by linarith) (hrmin.trans_le (hr j)).le
  have hYp (j : Fin N) : 0<Y j := zero_lt_one.trans_le (hY j)
  have hphase (j : Fin N) := hb j d hd hd' hU hZ.2 η u hulo hcal huhi a i hi ha ha1 hbin (r j) t (hr j) (hr' j) ht
  refine ⟨fun j=>⟨(hphase j).1,(hphase j).2.1,(hphase j).2.2.1,(hphase j).2.2.2.1,(hphase j).2.2.2.2.1⟩,?_⟩
  let p : Fin N→ℝ := fun j=>(Y j)^(g j+mesh)
  have hp (j : Fin N) : 1≤p j := Real.one_le_rpow (hY j) (by have := (hphase j).1;dsimp [g];linarith)
  have hph (j : Fin N) : ‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j := by
    have hj := (hphase j).2.2.2.2.2
    have hsum : phaseSlot u (T j) (W j) (Y j) z=
        ∑P∈T j,W j ((P.val.absNorm:ℝ)/Y j)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val)) :=
      Finset.sum_coe_sort (T j) (fun P=>W j ((P.val.absNorm:ℝ)/Y j)*(P.val.absNorm:ℂ)^(z-1)*
        (-star (CanonicalRowCompletion.idealRowHom u.val P.val)))
    have hj' : ‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ)+g j+mesh) := by
      rw [hsum]
      convert hj using 1
      simp only [Y,g,z]
      congr 1
      norm_num
    apply hj'.trans_eq
    dsimp only [p]
    rw [←Real.rpow_add (hYp j)]
    congr 1
    ring
  have hgood (j : Fin N) (P : PrimeIdeal) (hP : P∈T j) := hg (RayQuotient.identityClass M H) S d (r j) hd (hr j) P hP
  have hfreq := cube_buffered_heights t ((3*i+1:ℕ)*Z^τ) (Z^τ) i ht
    (Real.rpow_nonneg (zero_le_one.trans hZ.1) _) (by push_cast;have hh : 0≤Z^τ := Real.rpow_nonneg (zero_le_one.trans hZ.1) _;nlinarith)
  have hbound' := hbound u hu η (rayCubeFamily M H hH u) (Z^τ) a i hZ.2 ha ha1 hbin T
    (poolOutside M H S N c b Y) hdis (fun j P hP=>(hgood j P hP).2.1)
    (fun j P hP=>(hgood j P hP).2.2.1) (fun j P hP=>(hgood j P hP).2.2.2)
    W Y hY (fun j=>(hWs j).trans Ioo_subset_Icc_self) hWB
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I) z
    (by simp) (by simp) (by simp [z]) (by simpa using hfreq.1) (by simpa using hfreq.2.1) p hp hph
  have hprod : (∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)=∏j,(Y j)^(-(4/25:ℝ)+g j+mesh) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    dsimp only [p]
    rw [←Real.rpow_add (hYp j)]
    congr 1
    ring
  calc
    _ ≤ C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*
        (3+(3*i+2:ℕ)*Z^τ)^(2+4*eps)*((∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := by
      exact hbound'.trans_eq (by ring)
    _ ≤ C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*
        ((∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg
        (Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (hYp j).le _))
        (Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))))
      exact mul_le_mul_of_nonneg_left (hheightZ i hi) (by unfold rowNorm;positivity)
    _ = _ := by rw [hprod]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2271

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CubeFixedPrimes.lean; sha256: f6fe5e084a764b4732fe2c6a67b80ee898c493c1451e3ea6100c348ddecd2857 -/
section Source2272
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots ProbeCentralAllSlots HeckePrimeAmplitudeBins
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem fixedPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_fixed_cube_prime_bound (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (_hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(u : FreeRow),u.val≠1 → Z^δ≤rowNorm u →
      (calibrationForSet S hmax).residueMonoid u.val≠0 → rowNorm u≤Z^(d-margin) →
      ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let x : ℂ := (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I)
      let w : ℂ := (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      let Q : Fin N→ℂ := fun j=>HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z
      let g : Fin N→ℝ := fun j=>amplitude (Y j) (a-1/2) mesh (Q j)
      (∀j,0≤g j ∧ g j≤a-1/2 ∧ g j∈labels (a-1/2) mesh ∧
        ‖Q j‖≤(Y j)^(g j+mesh) ∧ (0<g j → (Z^d)^(2*(ell j/d)*g j)≤‖Q j‖^2)) ∧
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=>fixedPoolOutside M H S N c b Y j (P j).val (P j).property) W Y x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*
          (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh)) := by
  obtain ⟨C,hC,hbound⟩ := actual_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax W hWs hW hWB
  have hdj := power_pools_eventually_disjoint (RayQuotient.identityClass M H) S
    (fun _ : Fin N=>c) (fun _=>b) ell (fun _=>hc) (fun _=>hcb) hell
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hbound η,hdj,eventually_ge_atTop (1:ℝ)] with Z hbound hdis hZ
  intro d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin
  dsimp only
  intro t ht
  have hd0 : 0<d := hdmin.trans_le hd
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hr (j : Fin N) : rmin≤ell j/d := by
    apply (le_div_iff₀ hd0).mpr
    exact (by nlinarith [mul_le_mul_of_nonneg_right hd' hrmin.le] : rmin*d≤dmax*rmin).trans (hello j)
  have hr' (j : Fin N) : ell j/d≤R := by
    apply (div_le_iff₀ hd0).mpr
    exact (hellhi j).trans (by nlinarith [mul_le_mul_of_nonneg_right hd hR])
  have heq (j : Fin N) : (Z^d)^(ell j/d)=Z^(ell j) := by
    rw [←Real.rpow_mul hZp.le,mul_div_cancel₀ _ hd0.ne']
  have hb := hbound d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin (fun j=>ell j/d) hr hr'
  have hfun : (fun j : Fin N => (Z^d)^(ell j/d)) = (fun j => Z^(ell j)) := funext heq
  rw [hfun] at hb
  exact hb hdis t ht

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2272

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CubeSlotExponent.lean; sha256: fcbf599c51475455f27ccc157f023268cf927aa8617e5a8a04d1f87c962e387e -/
section Source2273
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeDetectorPhysicalSelection

lemma source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=1/6) :
    (∑j∈slots,ell j/d)=1/(6*d) := by
  rw [←Finset.sum_div,hell]
  ring

lemma source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=1/6) :
    weightedMean slots (fun j=>ell j/d) g=6*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  field_simp

lemma source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0<Z) (hd : d≠0) (hell : ∑j∈slots,ell j=1/6) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-(2/75:ℝ)+weightedMean slots (fun j=>ell j/d) g/6+mesh/6) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  ring

lemma source_slot_spike_scale (Z d ell g : ℝ) (hZ : 0≤Z) (hd : d≠0) :
    (Z^d)^(2*(ell/d)*g)=Z^(2*ell*g) := by
  rw [←Real.rpow_mul hZ]
  congr 1
  field_simp

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2273

/- Original source: OAI/NumberTheory/DirichletL/Detector/CentralClassArithmetic.lean; sha256: f58267253e1b165a56047c50f88e68e1ce7a71db7d038ee9d9a19e74ccab568f -/
section Source2274
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem classPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_class_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v a q D Rcount : ℝ),0≤v → 51/100≤a → a≤1 → 0≤D → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      (rows.card:ℝ)≤D*(Z^d)^Rcount →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      (∀u∈rows,weightedMean Finset.univ (fun j=>ell j/d)
        (fun j=>HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) ((17/50:ℂ)+t.1.2*Complex.I)))=q) →
      ‖cubeArithmeticSum S hS hmax η rows T (classPoolOutside M H S N c b Y) W Y a e t‖≤
        C*D*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(d*Rcount+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6) := by
  obtain ⟨C,hC,hbound⟩ := actual_fixed_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
  let AA : ℝ := max 1 ((2:ℝ)^(4/25+12*e+eps*(N+8)))
  have hAA : 0<AA := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C*AA,mul_pos hC hAA,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v a q D Rcount hv ha ha' hD rows hrows hnorm hcard i hi hbin
  dsimp only
  intro t ht hq
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hd0 : 0<d := hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let α : ℝ := a-1/2+12*e+eps*(N+8)
  let F : FreeRow→ℝ := fun u=>‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
    (fun j=>classPoolOutside M H S N c b Y j _ (P j).property) W Y
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I) z‖
  let E : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^loss*Z^(-2/75+q/6+mesh/6)
  have hE : 0≤E := by dsimp [E];positivity
  have hF (u : FreeRow) (hu : u∈rows) : F u≤E*rowNorm u^α := by
    rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi a i hi ha ha' (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N→ℝ := fun j=>HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
    have hp : (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=Z^(-2/75+q/6+mesh/6) := by
      rw [show (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=
        Z^(-(2/75:ℝ)+weightedMean Finset.univ (fun j=>ell j/d) g/6+mesh/6) from
        source_slot_product Finset.univ ell g Z d mesh hZp hd0.ne' hellsum]
      rw [show weightedMean Finset.univ (fun j=>ell j/d) g=q from hq u hu]
      congr 1 ; ring
    have hh' := hh.2
    rw [hp] at hh'
    convert hh' using 1 ; dsimp [F,E,α,Y,z,g] ; ring
  have hh := dyadic_weighted_rows_card α (17/50) E (Z^v) (D*(Z^d)^Rcount) hE
    (Real.rpow_pos_of_pos hZp _) rows hcard hnorm F hF z (by simp [z])
  have hsum : ‖cubeArithmeticSum S hS hmax η rows T (classPoolOutside M H S N c b Y) W Y a e t‖≤
      ∑u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    unfold cubeArithmeticSum
    exact (norm_sum_le _ _).trans_eq (by apply Finset.sum_congr rfl;intro u hu;rw [norm_mul])
  have hAp : ProbeSelectedPrimeSums.annularPower 1 2 (α-17/50)≤AA :=
    annular_power_uniform _ _ (by dsimp [α];linarith)
  apply (hsum.trans hh).trans
  have hpow : (Z^d)^Rcount*Z^loss*Z^(-2/75+q/6+mesh/6)*(Z^v)^(α-17/50)=
      Z^(d*Rcount+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6) := by
    simp_rw [←Real.rpow_mul hZp.le]
    rw [←Real.rpow_add hZp,←Real.rpow_add hZp,←Real.rpow_add hZp]
    congr 1
    dsimp [α]
    ring
  calc
    _ ≤ (D*(Z^d)^Rcount)*E*AA*(Z^v)^(α-17/50) := by gcongr
    _ = _ := by
      dsimp [E]
      calc
        _ = (C*AA)*D*(η.modulus.absNorm:ℝ)^(2*eps)*
          ((Z^d)^Rcount*Z^loss*Z^(-2/75+q/6+mesh/6)*(Z^v)^(α-17/50)) := by ring
        _ = _ := by rw [hpow]
end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2274

/- Original source: OAI/NumberTheory/DirichletL/Detector/CentralClassPartition.lean; sha256: da2a07d3a4197a63bdb33874785ac439f6e9e15e029acd328726b62077bf21d2 -/
section Source2275
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

lemma sum_amplitudeRows {Slot : Type*} (rows : Finset FreeRow) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ)
    (f : FreeRow→ℂ) :
    (∑u∈rows,f u)=∑bin : BinLabel slots cap mesh,
      ∑u∈amplitudeRows rows slots U cap mesh hm widths Q bin,f u := by
  have hmap : ∀u∈rows,amplitudeLabel slots U cap mesh hm widths Q u∈
      (Finset.univ : Finset (BinLabel slots cap mesh)) := by simp
  exact (Finset.sum_fiberwise_of_maps_to hmap f).symm

lemma cubeArithmeticSum_amplitude_partition {N : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (rows : Finset FreeRow) (T : Fin N→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀j P,P∈T j→P.val∉S) (W : Fin N→ℝ→ℂ) (Yp : Fin N→ℝ)
    (a e : ℝ) (t : HeightSpace) (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0<mesh) (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ) :
    cubeArithmeticSum S hS hmax η rows T hT W Yp a e t=
      ∑bin : BinLabel slots cap mesh,cubeArithmeticSum S hS hmax η
        (amplitudeRows rows slots U cap mesh hm widths Q bin) T hT W Yp a e t := by
  unfold cubeArithmeticSum
  exact sum_amplitudeRows rows slots U cap mesh hm widths Q _

theorem cubeArithmeticSum_class_uniform {N : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (rows : Finset FreeRow) (T : Fin N→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀j P,P∈T j→P.val∉S) (W : Fin N→ℝ→ℂ) (Yp : Fin N→ℝ)
    (a e : ℝ) (t : HeightSpace) (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0<mesh) (hcap : cap≤1/2) (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ)
    (A : ℝ) (hA : 0≤A)
    (hclass : ∀bin : BinLabel slots cap mesh,
      (amplitudeRows rows slots U cap mesh hm widths Q bin).Nonempty →
      ‖cubeArithmeticSum S hS hmax η (amplitudeRows rows slots U cap mesh hm widths Q bin)
        T hT W Yp a e t‖≤A) :
    ‖cubeArithmeticSum S hS hmax η rows T hT W Yp a e t‖≤
      (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^slots.card*A := by
  rw [cubeArithmeticSum_amplitude_partition S hS hmax η rows T hT W Yp a e t slots U cap mesh hm widths Q]
  calc
    _ ≤ ∑bin : BinLabel slots cap mesh,A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro bin _
      by_cases hn : (amplitudeRows rows slots U cap mesh hm widths Q bin).Nonempty
      · exact hclass bin hn
      · have he := Finset.not_nonempty_iff_eq_empty.mp hn
        simpa only [he,cubeArithmeticSum,Finset.sum_empty,norm_zero] using hA
    _ = (Fintype.card (BinLabel slots cap mesh):ℝ)*A := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast HeckeDetectorClassBudget.bin_card_le slots cap mesh hcap hm
end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2275

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/NonfloorDictionary.lean; sha256: 44a8d09efc3e3ac4a43786d42f9ca4ad7e48849fd26f10681c54994536077ede -/
section Source2276
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorPhysicalSelection
open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O)
variable (H : Subgroup (O ⧸ M)ˣ)

lemma source_physical_amplitude {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b : ℝ) (z : ℂ) (hZ : 0<Z) (hd : d≠0) (u : FreeRow) (j : Fin N) :
    physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d) u j=
      HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z := by
  unfold physical
  rw [physical_slot_scale ell Z d hZ hd j]

lemma source_rowMean_eq {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b a mesh : ℝ) (z : ℂ) (hZ : 0<Z) (hd : d≠0) (u : FreeRow) :
    rowMean Finset.univ (Z^d) ((2*a-1)/2) mesh (fun j=>ell j/d)
      (physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)) u=
      weightedMean Finset.univ (fun j=>ell j/d)
        (fun j=>HeckePrimeAmplitudeBins.amplitude (Z^(ell j)) (a-1/2) mesh
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z)) := by
  unfold rowMean
  simp_rw [physical_slot_scale ell Z d hZ hd,source_physical_amplitude M H ell W Z d b z hZ hd]
  rw [show (2*a-1)/2=a-1/2 by ring]

lemma source_amplitude_class_mean {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b a mesh : ℝ) (z : ℂ) (hZ : 0<Z) (hd : d≠0) (hm : 0<mesh)
    (rows : Finset FreeRow) (bin : BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) mesh)
    (u : FreeRow)
    (hu : u∈amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hm (fun j=>ell j/d)
      (physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)) bin) :
    weightedMean Finset.univ (fun j=>ell j/d)
      (fun j=>HeckePrimeAmplitudeBins.amplitude (Z^(ell j)) (a-1/2) mesh
        (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z))=
      classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin := by
  rw [←source_rowMean_eq M H ell W Z d b a mesh z hZ hd u]
  exact rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2) mesh hm (fun j=>ell j/d) _ bin u hu

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2276

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/NonfloorBudget.lean; sha256: 0d175e0933a1d4dd2d42833952ca0409de6ffede8fff50324d7427d577d5cedb -/
section Source2277
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorClassBudget

lemma eventually_all_rpow_ge {P : ℝ→Prop} (hP : ∀ᶠU in atTop,P U)
    (dmin : ℝ) (hdmin : 0<dmin) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → P (Z^d) := by
  obtain ⟨A,hA⟩ := Filter.eventually_atTop.1 hP
  have hh := (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop A)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with Z hZ hZ1
  intro d hd
  exact hA _ (hZ.trans (Real.rpow_le_rpow_of_exponent_le hZ1 hd))

lemma source_count_frequency_eventually (n : ℕ) (dmax τ h : ℝ)
    (hdmax : 0<dmax) (hτ : 0<τ) (hh : τ<h) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,d≤dmax → ∀i : ℕ,i≤n →
      2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤Z^h := by
  have hC := HeckeDyadic.constant_absorbed_eventually
    (2*Real.pi+3*(n:ℝ)) (h-τ) (by linarith)
  filter_upwards [hC,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro d hd i hi
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hexp : d*(τ/(2*dmax))≤τ := by
    have h1 := mul_le_mul_of_nonneg_right hd (show 0≤τ/(2*dmax) by positivity)
    have h2 : dmax*(τ/(2*dmax))=τ/2 := by field_simp
    rw [h2] at h1
    linarith
  have hp : (Z^d)^(τ/(2*dmax))≤Z^τ := by
    rw [←Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ hexp
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  calc
    _ ≤ (2*Real.pi+3*(n:ℝ))*Z^τ := by push_cast; nlinarith [Real.pi_pos,Real.rpow_pos_of_pos hZp τ]
    _ ≤ Z^(h-τ)*Z^τ := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^h := by rw [←Real.rpow_add hZp];congr 1;ring

lemma source_fiberConstant_bound (C K Z heightCost momentCost : ℝ)
    (hC : 0≤C) (hZ : 1≤Z) (hh : 0≤heightCost) :
    fiberConstant (C*Z^momentCost) (Z^heightCost) K ≤
      (384*max 1 K)*C*Z^(heightCost+momentCost) := by
  have hp := Real.one_le_rpow hZ hh
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  unfold fiberConstant
  calc
    _ ≤ (192*(2*Z^heightCost)*(C*Z^momentCost))*max 1 K := by gcongr;linarith
    _ = _ := by rw [Real.rpow_add hZp];ring

lemma source_dyadic_cost_eventually (dmin dmax loss : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hl : 0<loss) :
    ∃K : ℝ,0≤K ∧ ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
      (dyadicLength (Z^d):ℝ)^2≤K*Z^loss := by
  obtain ⟨K,hK,hbound⟩ := dyadic_cost_eventually (loss/dmax) (by positivity)
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hbound dmin hdmin,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd'
  apply (hb d hd).trans
  apply mul_le_mul_of_nonneg_left _ hK
  rw [←Real.rpow_mul (zero_lt_one.trans_le hZ).le]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hh := mul_le_mul_of_nonneg_right hd' (show 0≤loss/dmax by positivity)
  simpa only [mul_div_cancel₀ _ hdmax.ne'] using hh

lemma source_count_prefactor_eventually {Label : Type*} [Fintype Label]
    (N : ℕ) (dmin dmax logCost heightCost momentCost binWidth K₀ : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hl : 0<logCost)
    (hh : 0≤heightCost) (_hb : 0<binWidth) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
      ∀(C a ε tstar T allowance : ℝ) (i : ℕ),0≤C → a≤1 →
      ∀{M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Slot : Type*}
        (B : Batch M H Label Slot (Z^d) a ε tstar T allowance i),
      B.slots.card≤N → B.binWidth=binWidth →
      (Fintype.card Label:ℝ)*(dyadicLength (Z^d):ℝ)^2*
        fiberConstant (C*Z^momentCost) (Z^heightCost) K₀*(Fintype.card B.Bin:ℝ) ≤
      K*C*Z^(logCost+heightCost+momentCost) := by
  obtain ⟨L,hL,hbound⟩ := source_dyadic_cost_eventually dmin dmax logCost hdmin hdmax hl
  let A : ℝ := (alphabetBound binWidth : ℕ)^N
  let K : ℝ := (Fintype.card Label:ℝ)*L*(384*max 1 K₀)*A
  have hA : 0≤A := by dsimp [A];positivity
  have hK : 0≤K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with Z hbound hZ
  intro d hd hd' C a ε tstar T allowance i hC ha M H Slot B hslots hbin
  have hbin' : (Fintype.card B.Bin:ℝ)≤A := by
    have h1 := bin_card_le B.slots ((2*a-1)/2) B.binWidth (by linarith) B.binWidth_pos
    rw [hbin] at h1
    have h2 : (alphabetBound binWidth)^B.slots.card≤(alphabetBound binWidth)^N :=
      Nat.pow_le_pow_right (by unfold alphabetBound;omega) hslots
    change (Fintype.card (HeckeDetectorFiberPartition.BinLabel B.slots ((2*a-1)/2) B.binWidth):ℝ)≤A
    rw [hbin]
    dsimp only [A]
    exact_mod_cast h1.trans h2
  have hf := source_fiberConstant_bound C K₀ Z heightCost momentCost hC hZ hh
  have hf0 : 0≤fiberConstant (C*Z^momentCost) (Z^heightCost) K₀ := by unfold fiberConstant; positivity
  calc
    _ ≤ (Fintype.card Label:ℝ)*(L*Z^logCost)*
        ((384*max 1 K₀)*C*Z^(heightCost+momentCost))*A := by
      gcongr
      exact hbound d hd hd'
    _ = K*C*Z^(logCost+heightCost+momentCost) := by
      simp only [Real.rpow_add (zero_lt_one.trans_le hZ)]
      dsimp [K]
      ring
    _ ≤ _ := by gcongr;linarith

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2277

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/NonfloorSourceCount.lean; sha256: e780443551d020a74fa3c572c7747db82337ee7f92066321df69486b21fb4ca2 -/
section Source2278
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff

theorem balanced_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm)
    (Label : Type*) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) :
    ∃c κ K : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε Δ ν C q : ℝ) (i : ℕ),i≤n → 51/100<a → 2*a-1≤5/6 → a≤1 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C →
      ∀{Slot : Type*} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK₀,hcount⟩ := balanced_adaptive_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨c,κ,K,hc,hc1,hκ,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ ν C q i hi ha haδ ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  have hcard := hcount d hd a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) Δ ν
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha haδ hε hε' hΔ hΔ' hν (by positivity)
    (by positivity) (hfreq d hd' i hi) B hne hq hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

theorem high_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm)
    (Label : Type*) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) :
    ∃c κ K : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε Δ C q : ℝ) (i : ℕ),i≤n → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C →
      ∀{Slot : Type*} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK₀,hcount⟩ := high_adaptive_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨c,κ,K,hc,hc1,hκ,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ C q i hi ha ha' hε hε' hC Slot B hslots hbin hmom
  have hcard := hcount d hd a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) Δ
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha ha' hε hε' (by positivity)
    (by positivity) (hfreq d hd' i hi) B hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

def adaptiveRowExponent (δ q Δ ε εm slotMesh ν : ℝ) : ℝ :=
  if δ≤5/6 then Endpoint.balancedRowCount δ (1/2-q/δ)+Δ/4+159*ε+εm+slotMesh+7*ν
  else 1-δ+78*ε+εm

theorem adaptive_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm)
    (Label : Type*) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) :
    ∃cB κB cH κH K : ℝ,0<cB ∧ cB≤1 ∧ 0<κB ∧ 0<cH ∧ cH≤1 ∧ 0<κH ∧ 0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε Δ ν C q : ℝ) (i : ℕ),i≤n → 51/100<a → a≤1 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C →
      ∀{Slot : Type*} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ (if 2*a-1≤5/6 then cB else cH) (if 2*a-1≤5/6 then κB else κH) (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(adaptiveRowExponent (2*a-1) q Δ ε εm B.mesh ν) := by
  obtain ⟨cB,κB,KB,hcB,hcB1,hκB,hKB,hbalanced⟩ := balanced_source_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
    Label N n dmin dmax τ logCost heightCost momentCost binWidth hdmin hdmax hτ hl hh hb
  obtain ⟨cH,κH,KH,hcH,hcH1,hκH,hKH,hhigh⟩ := high_source_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
    Label N n dmin dmax τ logCost heightCost momentCost binWidth hdmin hdmax hτ hl hh hb
  refine ⟨cB,κB,cH,κH,max KB KH,hcB,hcB1,hκB,hcH,hcH1,hκH,lt_of_lt_of_le hKB (le_max_left _ _),?_⟩
  filter_upwards [hbalanced,hhigh,eventually_ge_atTop (1:ℝ)] with Z hb hh hZ
  intro d hd hd' a ε Δ ν C q i hi ha ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  by_cases hδ : 2*a-1≤5/6
  · simp only [ite_eq_left hδ] at hmom
    have hc := hb d hd hd' a ε Δ ν C q i hi ha hδ ha' hε hε' hΔ hΔ' hν hC B hslots hbin hne hq hmom
    simp only [adaptiveRowExponent,ite_eq_left hδ]
    exact hc.trans (by gcongr;exact le_max_left _ _)
  · simp only [ite_eq_right hδ] at hmom
    have hc := hh d hd hd' a ε Δ C q i hi (lt_of_not_ge hδ) ha' hε hε' hC B hslots hbin hmom
    simp only [adaptiveRowExponent,ite_eq_right hδ]
    exact hc.trans (by gcongr;exact le_max_right _ _)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2278

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/NonfloorMoments.lean; sha256: 1a858768eee8f4568ac011680d3ec6b742228f75b21e8a24f39d5d28f759788c -/
section Source2279
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def SourceMomentsAt {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (Δ c κ C height εm : ℝ) : Prop :=
  ∀q : ℝ,∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z^d) a ε (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
    B.rows⊆rows → B.data=sourceMomentData M H hH S hS η →
    B.reverse=sourceMomentReverse M H → B.slots=Finset.univ →
    B.widths=(fun j=>ell j/d) → B.profile=W → B.upper=(fun _=>b) → B.external=(fun _=>z) →
    B.mesh=slotMesh → B.binWidth=binWidth →
    (∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      Moments (B.fiber bin j J K hne) Δ c κ C height εm

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2279
