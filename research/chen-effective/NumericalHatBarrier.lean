import NumericalReverseRatio
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1022LowerBarrier
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131iiQhatLocal

open scoped Classical BigOperators Interval
open Set Filter MeasureTheory Topology Real
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open Section10CanonicalXi Section10Lemma1022
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem numerical_kernel_growth {s : ℝ} (hS : 20000 ≤ s) :
    0 < s + 1 ∧ 1 < lowerKernel 1 1 12 s := by
  let E : ℝ := 1
  let c : ℝ := 4 * (E + 2)
  have hE : 1 ≤ E := le_refl _
  have he9 : Real.exp 9 ≤ (19683 : ℝ) := by
    calc
      _ = Real.exp 1 ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (3 : ℝ) ^ (9 : ℕ) := pow_le_pow_left₀ (Real.exp_pos 1).le
        (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 3)) 9
      _ = _ := by norm_num
  have hs : max E (Real.exp 9 + Real.exp 1 + 2) ≤ s := by
    apply max_le
    · dsimp [E]; linarith only [hS]
    · linarith only [he9, Real.exp_one_lt_d9, hS]
  have hmain : 0 < s + E ∧ 1 < lowerKernel 1 E c s := by
    have hsE : E ≤ s := le_trans (le_max_left _ _) hs
    have hsbig : Real.exp 9 + Real.exp 1 + 2 ≤ s :=
      le_trans (le_max_right _ _) hs
    have hsbase : Real.exp 1 + 2 ≤ s := by
      have he9 : 0 < Real.exp 9 := Real.exp_pos 9
      linarith
    have hspos : 0 < s := by
      have he : 0 < Real.exp 1 := Real.exp_pos 1
      linarith
    have hdenE : 0 < s + E := by linarith
    have hdene : 0 < s + Real.exp 1 := add_pos hspos (Real.exp_pos 1)
    have hcpos : 0 < c := by dsimp [c]; linarith
    let x : ℝ := xi (s - 1)
    let d : ℝ := c / (s + Real.exp 1)
    let A : ℝ := x + d
    have hsxm1 : Real.exp 9 ≤ s - 1 := by
      have he : 0 < Real.exp 1 := Real.exp_pos 1
      linarith
    have hsxm1one : 1 < s - 1 := by
      have he9one : 1 < Real.exp 9 := Real.one_lt_exp_iff.mpr (by norm_num)
      linarith
    have hx9 : 9 < x := by
      dsimp [x]
      have hlog := log_lt_xi
        ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 9)).trans hsxm1)
      have hlog9 : 9 ≤ Real.log (s - 1) := by
        have hp : 0 < s - 1 := lt_of_lt_of_le (Real.exp_pos 9) hsxm1
        rw [← Real.exp_log hp] at hsxm1
        exact Real.exp_le_exp.mp hsxm1
      linarith
    have hdpos : 0 < d := by dsimp [d]; positivity
    have hApos : 0 < A := by dsimp [A]; linarith
    have hratioLower : (1 / 2 : ℝ) ≤ (s - 1) / (s + Real.exp 1) := by
      apply (le_div_iff₀ hdene).2
      linarith [hsbase]
    have hdsm1 : 2 * (E + 2) ≤ d * (s - 1) := by
      have hm := mul_le_mul_of_nonneg_left hratioLower hcpos.le
      have heq : c * ((s - 1) / (s + Real.exp 1)) = d * (s - 1) := by
        dsimp [d]
        field_simp [ne_of_gt hdene]
      rw [heq] at hm
      dsimp [c] at hm
      linarith
    have hratioUpper : (s + E - 1) / (s + Real.exp 1) ≤ 2 := by
      apply (div_le_iff₀ hdene).2
      linarith [hsE, Real.exp_pos 1]
    have hdterm : d * (s + E - 1) ≤ 2 * c := by
      have hm := mul_le_mul_of_nonneg_left hratioUpper hcpos.le
      have heq : c * ((s + E - 1) / (s + Real.exp 1)) = d * (s + E - 1) := by
        dsimp [d]
        field_simp [ne_of_gt hdene]
      rw [heq] at hm
      simpa [mul_comm] using hm
    let q : ℝ := d * (s - 1) - (E + 1)
    have hq : E + 3 ≤ q := by dsimp [q]; linarith
    have hqpos : 0 < q := by linarith
    have hxq : 9 * (E + 3) < x * q := by
      have h1 := mul_lt_mul_of_pos_right hx9 hqpos
      have h2 := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 9)
      nlinarith
    have hmain : (s + E) * A < (1 + d) * (1 + (s - 1) * x) - 1 := by
      have hgap : d * (s + E - 1) < x * q := by
        have hcval : 2 * c = 8 * (E + 2) := by dsimp [c]; ring
        rw [hcval] at hdterm
        nlinarith
      dsimp [A, q] at hgap ⊢
      nlinarith
    have hxEq : Real.exp x - 1 = (s - 1) * x := by
      dsimp [x]
      exact xi_equation hsxm1one
    have hexpLower : (1 + d) * Real.exp x ≤ Real.exp A := by
      have h := Real.add_one_le_exp d
      have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos x).le
      rw [mul_comm (Real.exp x), ← Real.exp_add] at hm
      simpa [A, add_comm] using hm
    have hnumerator : (s + E) * A < Real.exp A - 1 := by
      calc
        (s + E) * A < (1 + d) * (1 + (s - 1) * x) - 1 := hmain
        _ = (1 + d) * Real.exp x - 1 := by rw [← hxEq]; ring
        _ ≤ Real.exp A - 1 := by linarith
    have hquotient : s + E < (Real.exp A - 1) / A :=
      (lt_div_iff₀ hApos).2 (by simpa [mul_comm] using hnumerator)
    have hphaseInt :
        (Real.exp A - 1) / A ≤
          ∫ t in s - 1..s, Real.exp (lowerPhase 1 c s - lowerPhase 1 c t) := by
      rw [← integral_exp_endpoint A s (ne_of_gt hApos)]
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (Real.continuous_exp.comp
          (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _
      · have hpcont : ContinuousOn (lowerPhase 1 c) (Icc (s - 1) s) :=
          (lowerPhase_continuousOn (show 0 ≤ s - 1 by linarith)).mono
            (by intro t ht; exact ht.1)
        have hpcontU : ContinuousOn (lowerPhase 1 c) (uIcc (s - 1) s) := by
          simpa [uIcc_of_le (by linarith : s - 1 ≤ s)] using hpcont
        have hdiff : ContinuousOn
            (fun u : ℝ => lowerPhase 1 c s - lowerPhase 1 c u)
            (uIcc (s - 1) s) :=
          continuousOn_const.sub hpcontU
        have hccomp : ContinuousOn
            (fun u : ℝ => Real.exp (lowerPhase 1 c s - lowerPhase 1 c u))
            (uIcc (s - 1) s) := by
          change ContinuousOn
            (Real.exp ∘ fun u : ℝ => lowerPhase 1 c s - lowerPhase 1 c u)
            (uIcc (s - 1) s)
          exact Real.continuous_exp.comp_continuousOn hdiff
        exact hccomp.intervalIntegrable
      · intro t ht
        apply Real.exp_le_exp.mpr
        have hinc := lowerPhase_increment_ge hcpos.le hsbase ht
        simpa [A, x, d, add_mul] using hinc
    have hintgt : s + E <
        ∫ t in s - 1..s, Real.exp (lowerPhase 1 c s - lowerPhase 1 c t) :=
      lt_of_lt_of_le hquotient hphaseInt
    refine ⟨hdenE, ?_⟩
    rw [lowerKernel]
    norm_num only [one_div]
    simpa only [div_eq_inv_mul, E, c, show (4 : ℝ) * (1 + 2) = 12 by norm_num] using (one_lt_div hdenE).2 hintgt


  simpa only [E, c, show (4 : ℝ) * (1 + 2) = 12 by norm_num] using hmain

theorem numerical_Qhat_local {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 4 ≤ s) :
    (s + 1) * section13Qhat H s ≥ ∫ t in s - 1..s, section13Qhat H t := by
  have hab : s - 1 ≤ s := by linarith
  have hqpos : 0 < section13AdjointPlus s := by
    dsimp [section13AdjointPlus]
    nlinarith [sq_nonneg (s - 1)]
  have hQcont : ContinuousOn (section13Qhat H) (Icc (s - 1) s) :=
    (section13Qhat_continuousOn hH.toSection13HatContract).mono (by
      intro t ht
      exact (by linarith [ht.1] : 0 < t))
  have hleftInt : IntervalIntegrable
      (fun t => section13AdjointPlus s * section13Qhat H t) volume (s - 1) s :=
    by
      have hc : ContinuousOn
          (fun t : ℝ => section13AdjointPlus s * section13Qhat H t)
          (Icc (s - 1) s) :=
        (continuousOn_const : ContinuousOn
          (fun _t : ℝ => section13AdjointPlus s) (Icc (s - 1) s)).mul hQcont
      rw [← uIcc_of_le hab] at hc
      exact hc.intervalIntegrable
  have hrightInt : IntervalIntegrable
      (fun t => section13AdjointPlus (t + 1) * section13Qhat H t) volume (s - 1) s := by
    have hqcont : ContinuousOn (fun t : ℝ => section13AdjointPlus (t + 1))
        (Icc (s - 1) s) :=
      ((continuous_id.add continuous_const).pow 2 |>.sub
        (continuous_const.mul (continuous_id.add continuous_const)) |>.add
        continuous_const).continuousOn
    have hc := hqcont.mul hQcont
    rw [← uIcc_of_le hab] at hc
    exact hc.intervalIntegrable
  have hweighted :
      section13AdjointPlus s *
          (∫ t in s - 1..s, section13Qhat H t) ≤
        ∫ t in s - 1..s,
          section13AdjointPlus (t + 1) * section13Qhat H t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab hleftInt hrightInt
    intro t ht
    exact mul_le_mul_of_nonneg_right
      (section13AdjointPlus_window_lower hs ht)
      (section13Qhat_pos hH.toSection13HatContract (by linarith [ht.1])).le
  have hpair := section13Qhat_pairing_zero hH (by linarith : 3 < s)
  simp only [section10SignedPairing, one_mul, sub_eq_zero] at hpair
  have hsQ :
      (∫ t in s - 1..s, section13Qhat H t) ≤ s * section13Qhat H s := by
    apply (mul_le_mul_iff_of_pos_left hqpos).mp
    calc
      section13AdjointPlus s *
          (∫ t in s - 1..s, section13Qhat H t) ≤
          ∫ t in s - 1..s,
            section13AdjointPlus (t + 1) * section13Qhat H t := hweighted
      _ = section13AdjointPlus s * (s * section13Qhat H s) := by
        rw [← hpair]
        ring
  have hQpos := section13Qhat_pos hH.toSection13HatContract (by linarith : 0 < s)
  nlinarith



@[irreducible] noncomputable def numericalBarrierFloor : ℝ := 2 * compactHatLower 20000

theorem numericalBarrierFloor_pos : 0 < numericalBarrierFloor := by
  unfold numericalBarrierFloor
  exact mul_pos (by norm_num) (compactHatLower_pos (by norm_num : 3 ≤ (20000 : ℕ)))

theorem canonicalXi_nonneg (s : ℝ) : 0 ≤ xi s :=
  (etaOrderIso.symm ⟨max s 1, le_max_right s 1⟩).property

theorem numerical_Qhat_barrier {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 20000 ≤ s) :
    numericalBarrierFloor * Real.exp (-(∫ t in (1 : ℝ)..s, xi t) - 12 * Real.log (s + Real.exp 1)) <
      section13Qhat H s := by
  let f := section13Qhat H
  let g := lowerWeighted f 1 12
  have hf : ContinuousOn f (Ici (1 : ℝ)) :=
    (section13Qhat_continuousOn hH.toSection13HatContract).mono
      (fun _ hx => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx)
  have hg : ContinuousOn g (Ici (20000 - 1 : ℝ)) :=
    (lowerWeighted_continuousOn (b := (1 : ℝ)) (c := (12 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1) hf).mono
      (by intro x hx; change (1 : ℝ) ≤ x; have hh : (20000 - 1 : ℝ) ≤ x := hx; linarith only [hh])
  have hinit : ∀ t ∈ Icc (20000 - 1 : ℝ) 20000, numericalBarrierFloor ≤ g t := by
    intro t ht
    have htp := numerical_hat_compact hH.toSection13HatContract (m := 20000) (by norm_num) .plus
      (by linarith only [ht.1]) ht.2
    have htm := numerical_hat_compact hH.toSection13HatContract (m := 20000) (by norm_num) .minus
      (by linarith only [ht.1]) ht.2
    have hQ : numericalBarrierFloor ≤ f t := by
      unfold numericalBarrierFloor
      dsimp [f, section13Qhat]
      linarith only [htp, htm]
    have hphase : 0 ≤ lowerPhase 1 12 t := by
      unfold lowerPhase
      apply add_nonneg
      · apply intervalIntegral.integral_nonneg (by linarith only [ht.1])
        intro u _
        exact canonicalXi_nonneg _
      · apply mul_nonneg (by norm_num)
        exact Real.log_nonneg (by linarith only [ht.1, Real.exp_pos 1])
    have hQ0 : 0 ≤ f t := (numericalBarrierFloor_pos.le.trans hQ)
    have hh := mul_le_mul_of_nonneg_left (Real.one_le_exp hphase) hQ0
    change _ ≤ f t * Real.exp (lowerPhase 1 12 t)
    linarith only [hh, hQ]
  have hboost (u : ℝ) (hu : (20000 : ℝ) ≤ u)
      (hfloor : ∀ t ∈ Icc (u - 1) u, numericalBarrierFloor ≤ g t) : numericalBarrierFloor < g u := by
    have hk := numerical_kernel_growth hu
    apply weighted_strict_growth (b := (1 : ℝ)) (E := (1 : ℝ)) (c := (12 : ℝ))
      (by norm_num) hk.1 (by linarith only [hu])
      (hf.mono (by intro t ht; change (1 : ℝ) ≤ t; linarith only [ht.1, hu])) _ hk.2 hfloor numericalBarrierFloor_pos
    simpa only [one_mul] using numerical_Qhat_local hH (show 4 ≤ u by linarith only [hu])
  have hb := least_downward_crossing hg hinit hboost s hs
  dsimp [g, lowerWeighted, lowerPhase, f] at hb
  simp only [div_one] at hb
  have hm := mul_lt_mul_of_pos_right hb
    (Real.exp_pos (-(∫ t in (1 : ℝ)..s, xi t) - 12 * Real.log (s + Real.exp 1)))
  have heq : Real.exp ((∫ t in (1 : ℝ)..s, xi t) + 12 * Real.log (s + Real.exp 1)) *
      Real.exp (-(∫ t in (1 : ℝ)..s, xi t) - 12 * Real.log (s + Real.exp 1)) = 1 := by
    rw [← Real.exp_add]
    rw [show ((∫ t in (1 : ℝ)..s, xi t) + 12 * Real.log (s + Real.exp 1)) +
      (-(∫ t in (1 : ℝ)..s, xi t) - 12 * Real.log (s + Real.exp 1)) = 0 by ring, Real.exp_zero]
  have hr : (section13Qhat H s * Real.exp ((∫ t in (1 : ℝ)..s, xi t) + 12 * Real.log (s + Real.exp 1))) *
      Real.exp (-(∫ t in (1 : ℝ)..s, xi t) - 12 * Real.log (s + Real.exp 1)) = section13Qhat H s := by
    rw [mul_assoc, heq, mul_one]
  rwa [hr] at hm

#print axioms numerical_Qhat_barrier
end ChenEffective
