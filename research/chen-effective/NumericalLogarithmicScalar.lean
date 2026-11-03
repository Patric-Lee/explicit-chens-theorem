import NumericalJointEnvelope
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseABoundedK

noncomputable section
namespace ChenEffective
open Real Set
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def logarithmicBudget (A : ℝ) : ℝ := max 1 A
def logarithmicR (A K : ℝ) : ℝ := 2*logarithmicBudget A*(1+2*K)
def logarithmicScalarConstant (A K : ℝ) : ℝ :=
  7*(logarithmicR A K)^3*(logarithmicBudget A)^4/jointEnvelopeFloor A

theorem logarithmicScalarConstant_pos {A K : ℝ} (hK : 0 < K) : 0 < logarithmicScalarConstant A K := by
  have hB : 1 ≤ logarithmicBudget A := le_max_left _ _
  unfold logarithmicScalarConstant logarithmicR
  exact div_pos (by positivity) (jointEnvelopeFloor_pos A)

theorem numerical_logarithmic_bounds {q : ℕ} {A K : ℝ} (hq : 2 ≤ q) (hK : 0 < K)
    (hA : Real.log (q : ℝ) ≤ A) :
    (Real.log (q : ℝ)/Real.log 2)*(1+K/Real.log 2) ≤ logarithmicR A K ∧
      sourceSigma (q : ℝ) 16 ≤ 7*(logarithmicBudget A)^2 ∧
      1/logarithmicBudget A ≤ (Real.log (q : ℝ))^(-(1/2 : ℝ)) := by
  let B := logarithmicBudget A
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hL : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hLB : Real.log (q : ℝ) ≤ B := hA.trans (le_max_right _ _)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have htwo : (Real.log (2 : ℝ))⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀' hlog2]
    linarith only [Real.log_two_gt_d9]
  have hLL : Real.log (q : ℝ)/Real.log 2 ≤ 2*B := by
    have hh := mul_le_mul_of_nonneg_right htwo hL.le
    simp only [div_eq_mul_inv] at *
    nlinarith only [hh,hLB]
  have hKK : K/Real.log 2 ≤ 2*K := by
    simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_right htwo hK.le
  refine ⟨?_,?_,?_⟩
  · unfold logarithmicR
    have hb : 1+K/Real.log 2 ≤ 1+2*K := by linarith only [hKK]
    exact mul_le_mul hLL hb (by positivity) (by positivity)
  · have hpow : Real.log (q : ℝ)^(1/16 : ℝ) ≤ B :=
      (Real.rpow_le_rpow hL.le hLB (by norm_num)).trans (Real.rpow_le_self_of_one_le hB (by norm_num))
    have h27 : 1 ≤ Real.log (27 : ℝ) := one_le_log_three.trans (Real.log_le_log (by norm_num) (by norm_num))
    have h27u : Real.log (27 : ℝ) ≤ 6 := by
      rw [show (27 : ℝ)=3^3 by norm_num,Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
    have heq : Real.log (27*(q : ℝ)) = Real.log 27+Real.log (q : ℝ) := Real.log_mul (by norm_num) hq0.ne'
    have hi0 : 0 < Real.log (27*(q : ℝ)) := by rw [heq]; linarith only [h27,hL]
    have hll0 : 0 ≤ Real.log (Real.log (27*(q : ℝ))) := Real.log_nonneg (by rw [heq]; linarith only [h27,hL])
    have hll : Real.log (Real.log (27*(q : ℝ))) ≤ 7*B := by
      have hh := Real.log_le_sub_one_of_pos hi0
      rw [heq] at hh ⊢
      linarith only [hh,h27u,hLB,hB]
    unfold sourceSigma
    simpa only [show (1/(16 : ℝ))=(1/16 : ℝ) by rfl,pow_two,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul hpow hll hll0 hB0.le
  · have hsqrt : Real.sqrt (Real.log (q : ℝ)) ≤ B :=
      (Real.sqrt_le_sqrt hLB).trans (Real.sqrt_le_self_iff.mpr (Or.inr hB))
    rw [Real.rpow_neg hL.le,← Real.sqrt_eq_rpow,one_div]
    exact (inv_le_inv₀ hB0 (Real.sqrt_pos.mpr hL)).mpr hsqrt

theorem numerical_source_factorial_bound {q p : ℕ} {K x : ℝ}
    (hq : 2 ≤ q) (hK : 0 < K) (hp : p=⌈(q : ℝ)^(1/x)⌉₊) (hx : 2 ≤ x) :
    suzukiSourceL (p : ℝ) K^(⌊x-2⌋₊+1)/((⌊x-2⌋₊+1).factorial : ℝ)*Real.exp (suzukiSourceL (p : ℝ) K) ≤
      ((Real.log (q : ℝ)/Real.log 2)*(1+K/Real.log 2))^2 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hL : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hp2 : 2 ≤ p := by
    rw [hp]
    have hh := Real.one_lt_rpow hq1 (one_div_pos.mpr (by linarith only [hx] : 0 < x))
    have ht : 1 < ⌈(q : ℝ)^(1/x)⌉₊ := Nat.lt_ceil.mpr (by simpa using hh)
    omega
  have hLp : 0 ≤ suzukiSourceL (p : ℝ) K := by
    have hplog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ p by exact_mod_cast hp2)
    have hfirst : 0 ≤ Real.log (Real.log (p : ℝ)/Real.log 2) :=
      Real.log_nonneg ((le_div_iff₀ hlog2).mpr (by simpa using hplog))
    have hsecond : 0 ≤ Real.log (1+K/Real.log 2) := Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    exact add_nonneg hfirst hsecond
  have hmono : suzukiSourceL (p : ℝ) K ≤ suzukiSourceL (q : ℝ) K := by
    rw [hp]
    exact suzukiSourceL_natCeil_rpow_le hq hx
  have hexp : Real.exp (suzukiSourceL (q : ℝ) K) = (Real.log (q : ℝ)/Real.log 2)*(1+K/Real.log 2) := by
    unfold suzukiSourceL
    rw [Real.exp_add,Real.exp_log (by positivity),Real.exp_log (by positivity)]
  have hterm := Real.pow_div_factorial_le_exp (suzukiSourceL (p : ℝ) K) hLp (⌊x-2⌋₊+1)
  calc
    _ ≤ Real.exp (suzukiSourceL (p : ℝ) K)*Real.exp (suzukiSourceL (p : ℝ) K) :=
      mul_le_mul_of_nonneg_right hterm (Real.exp_pos _).le
    _ ≤ Real.exp (suzukiSourceL (q : ℝ) K)*Real.exp (suzukiSourceL (q : ℝ) K) := by gcongr
    _ = _ := by rw [hexp]; ring

theorem numerical_uniform_log_scalar (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    {A K : ℝ} (hK : 0 < K) (S : BoundingSieve) (hlocal : HasDimensionOneLocalProductBound S K)
    (n q p : ℕ) (x : ℝ) (hq : 2 ≤ q) (hp : p=⌈(q : ℝ)^(1/x)⌉₊) (hx : 2 ≤ x)
    (hA : Real.log (q : ℝ) ≤ A) :
    suzukiSourceL (p : ℝ) K^(⌊x-2⌋₊+1)/((⌊x-2⌋₊+1).factorial : ℝ)*Real.exp (suzukiSourceL (p : ℝ) K) ≤
      logarithmicScalarConstant A K*claim14_5Scale S H n (q : ℝ) 16 (1/2) (sourceSigma (q : ℝ) 16) K x := by
  let B := logarithmicBudget A
  let R := logarithmicR A K
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hR : 0 < R := by dsimp [R,logarithmicR]; positivity
  have hL : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hLB : Real.log (q : ℝ) ≤ B := hA.trans (le_max_right _ _)
  have hsigma : 0 < sourceSigma (q : ℝ) 16 := sourceSigma_pos_of_nat_two_le hq
  obtain ⟨hRq,hSig,hTail⟩ := numerical_logarithmic_bounds hq hK hA
  have hV : 1/R ≤ claim14_5VProduct S (q : ℝ) := by
    have hRq0 : 0 < (Real.log (q : ℝ)/Real.log 2)*(1+K/Real.log 2) := by positivity
    have hbase := claim14_5VProduct_lower_of_localProduct (S := S) (D := (q : ℝ)) (K := K)
      (by exact_mod_cast hq) hlocal
    have hi : 1/R ≤ 1/((Real.log (q : ℝ)/Real.log 2)*(1+K/Real.log 2)) :=
      one_div_le_one_div_of_le hRq0 hRq
    exact hi.trans ((div_le_iff₀ hRq0).mpr (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hbase))
  have hrest : 1/(7*B^3) ≤ Real.exp (Real.sqrt K)/(Real.log (q : ℝ)*sourceSigma (q : ℝ) 16) := by
    have hden : Real.log (q : ℝ)*sourceSigma (q : ℝ) 16 ≤ 7*B^3 := by
      have hh := mul_le_mul hLB hSig hsigma.le hB0.le
      nlinarith only [hh]
    have he : 1 ≤ Real.exp (Real.sqrt K) := Real.one_le_exp (Real.sqrt_nonneg _)
    exact (one_div_le_one_div_of_le (mul_pos hL hsigma) hden).trans
      (div_le_div_of_nonneg_right he (by positivity))
  have hE := numerical_joint_envelope hH.toSection13HatContract (by exact_mod_cast hq) hA n hx
  have hscale : jointEnvelopeFloor A/(7*R*B^4) ≤
      claim14_5Scale S H n (q : ℝ) 16 (1/2) (sourceSigma (q : ℝ) 16) K x := by
    unfold claim14_5Scale
    calc
      _ = (1/R)*(1/(7*B^3))*jointEnvelopeFloor A*(1/B) := by field_simp
      _ ≤ _ := by
        have hv0 := (show 0 < 1/R by positivity).le.trans hV
        have hf0 := (jointEnvelopeFloor_pos A).le
        have he0 := hf0.trans hE
        gcongr
  have hleft := (numerical_source_factorial_bound hq hK hp hx).trans
    (pow_le_pow_left₀ (by positivity) hRq 2)
  have hc : 0 < logarithmicScalarConstant A K := logarithmicScalarConstant_pos hK
  have hh := mul_le_mul_of_nonneg_left hscale hc.le
  have heq : logarithmicScalarConstant A K*(jointEnvelopeFloor A/(7*R*B^4))=R^2 := by
    unfold logarithmicScalarConstant
    change 7*R^3*B^4/jointEnvelopeFloor A*(jointEnvelopeFloor A/(7*R*B^4))=R^2
    field_simp [(jointEnvelopeFloor_pos A).ne',hR.ne',hB0.ne']
  rw [heq] at hh
  exact hleft.trans hh

#print axioms numerical_uniform_log_scalar
end ChenEffective
