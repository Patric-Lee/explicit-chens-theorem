import GRHQuarterChenPair

/- Component: GRHQuarterChenHigh -/
noncomputable section
namespace ChenEffective.GRHQuarterChen.High
open Classical Complex Finset Filter MeasureTheory
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open ChenEffective.NumericalPanHigh
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
theorem numerical_high_log_four {N : ℕ} (hN : GRHQuarterChen.targetCutoff≤ N) : 4≤ Real.log (N:ℝ) := by
  have h := GRHQuarterChen.target_log_lower hN
  linarith only [h]
theorem numerical_source_power {B N : ℕ} (hN : GRHQuarterChen.targetCutoff≤ N) (hB : B≤38) :
    (N : ℝ)^(2/3 : ℝ) ≤ upperConductor N (B : ℝ)^2 := by
  have hL := numerical_high_log_four hN
  have hl0 : 0 < Real.log (N : ℝ) := by linarith only [hL]
  have hN9 := GRHQuarterChen.target_nine_le hN
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hp := GRHQuarterChen.log_power_at_target hN (k:=2*B) (by omega) (δ:=1/3) (by norm_num)
  have heq : lowConductor N (B : ℝ)^2 = Real.log (N : ℝ)^(2*B) := by
    rw [lowConductor, Real.rpow_natCast, ← pow_mul, Nat.mul_comm B 2]
  rw [upperConductor_square, le_div_iff₀ (by unfold lowConductor; positivity), heq]
  calc
    _ ≤ (N : ℝ)^(2/3 : ℝ) * (N : ℝ)^(1/3 : ℝ) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hN0.le _)
    _ = _ := by rw [← Real.rpow_add hN0]; norm_num

theorem numerical_source_cell_uniform (B N : ℕ) (hN : GRHQuarterChen.targetCutoff≤ N) (hB : B≤38)
    (j m A₁ A₂ k : ℕ) (f : ℕ → ℂ) (hAN : A₂ ≤ N)
    (hRD : conductorRadius N (B : ℝ) j ≤ upperConductor N (B : ℝ))
    (hA : (A₂ : ℝ) ≤ (N : ℝ)^(2/3 : ℝ))
    (hAlow : Real.log (N : ℝ)^((2 : ℝ)*B) ≤ A₁)
    (hf : ∀ n, ‖f n‖ ≤ 1) :
    sourceCell f m N A₁ A₂ k (conductorRadius N (B : ℝ) j) ≤
      6*liuPanPerronHalfStep N^(1/2 : ℝ)*
        (panShortConstant*Real.sqrt N*Real.log N^(1-(B : ℝ)))*Real.log (1+panSourceHeight N) +
      6*liuPanPerronHalfStep N^panSourceSigma N*
        (panLongConstant*Real.log N^2/Real.log N^(B : ℝ))*Real.log (1+panSourceHeight N) +
      776/(N : ℝ) := by
  have hlog := numerical_high_log_four hN
  have hl1 : 1 ≤ Real.log (N : ℝ) := by linarith only [hlog]
  have hNpos : 1 ≤ N := source_pos_of_log hl1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR := conductorRadius_ge_one j hl1 (Nat.cast_nonneg B)
  have hH := shortCutoff_le_x hl1 (Nat.cast_nonneg B) (by linarith only [hR]) hRD
  obtain ⟨_, rfl, _, hlong⟩ := NumericalPanHigh.chosen_long_mean_uniform
  have hmain := source_cell_bound_of_means f hf m A₁ A₂ k hlog hNpos le_rfl hAN hR hH
    (show 0 ≤ panShortConstant*Real.sqrt N*Real.log N^(1-(B : ℝ)) by
      unfold panShortConstant; have hh := panSharpConstant_pos; positivity)
    (show 0 ≤ panLongConstant*Real.log N^2/Real.log N^(B : ℝ) by
      unfold panLongConstant; have hh := panSharpConstant_pos; positivity)
    (fun s hs => shortMean_le_log_scale f hf m A₁ A₂ k N (Nat.cast_nonneg B) hl1 hR hRD
      (hA.trans (numerical_source_power hN hB)) s hs)
    (fun s hs => hlong (B : ℝ) N N j m A₁ A₂ k f s (Nat.cast_nonneg B) hl1 le_rfl hAlow hf hs)
  apply hmain.trans
  apply add_le_add le_rfl
  have hRx : conductorRadius N (B : ℝ) j ≤ (N : ℝ) :=
    hRD.trans ((upperConductor_le_sqrt hl1 (Nat.cast_nonneg B)).trans
      (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hNpos))))
  calc
    _ ≤ 2*(N : ℝ)*(388/(N : ℝ)^2) := by gcongr
    _ = _ := by field_simp; norm_num

theorem numerical_source_cell_log_saving (B x : ℕ) (hx : GRHQuarterChen.targetCutoff≤ x) (hBcap : B≤38)
    (j m A₁ A₂ k : ℕ) (f : ℕ → ℂ)
    (hAx : A₂ ≤ x) (hRD : conductorRadius x (B : ℝ) j ≤ upperConductor x (B : ℝ))
    (hApower : (A₂ : ℝ) ≤ (x : ℝ)^(2/3 : ℝ))
    (hAlow : Real.log (x : ℝ)^((2 : ℝ)*B) ≤ A₁) (hf : ∀ n, ‖f n‖ ≤ 1) :
    sourceCell f m x A₁ A₂ k (conductorRadius x (B : ℝ) j) ≤
      panCellConstant * x * Real.log x^(4-(B : ℝ)) + 776/(x : ℝ) := by
  have hxlog := numerical_high_log_four hx
  have hCs : 0 < panShortConstant := by unfold panShortConstant; exact mul_pos (by norm_num) panSharpConstant_pos
  have hCl : 0 < panLongConstant := by unfold panLongConstant; have := panSharpConstant_pos; positivity
  have hxlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hxpos := source_pos_of_log hxlog1
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hxpos
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hmain := numerical_source_cell_uniform B x hx hBcap j m A₁ A₂ k f hAx hRD hApower hAlow hf
  have hsqrt : liuPanPerronHalfStep x ^ (1 / 2 : ℝ) ≤ 2 * Real.sqrt x := by
    rw [← Real.sqrt_eq_rpow]
    have hsq := Real.sq_sqrt (halfStep_pos x).le
    have hxq := Real.sq_sqrt hx0.le
    have hp := Real.sqrt_nonneg (liuPanPerronHalfStep x)
    have hxp := Real.sqrt_nonneg (x : ℝ)
    unfold liuPanPerronHalfStep at hsq hp ⊢
    nlinarith
  have hlogT := log_source_height_le hxlog1
  have hlognonneg : 0 ≤ Real.log (1 + panSourceHeight x) :=
    Real.log_nonneg (by have : 0 < panSourceHeight x := Real.exp_pos _; linarith)
  have hshort :
      6 * liuPanPerronHalfStep x ^ (1 / 2 : ℝ) *
          (panShortConstant * Real.sqrt x * Real.log x ^ (1 - (B : ℝ))) * Real.log (1 + panSourceHeight x) ≤
        36 * panShortConstant * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) := by
    calc
      _ ≤ 6 * (2 * Real.sqrt x) * (panShortConstant * Real.sqrt x * Real.log x ^ (1 - (B : ℝ))) *
          (3 * (Real.log x) ^ 2) := by gcongr
      _ = 36 * panShortConstant * (x : ℝ) * Real.log x ^ (3 - (B : ℝ)) := by
        rw [show (3 - (B : ℝ) : ℝ) = (1 - (B : ℝ)) + 2 by ring, Real.rpow_add hlogpos,
          Real.rpow_two]
        calc
          _ = 36 * panShortConstant * (Real.sqrt (x : ℝ)) ^ 2 *
              (Real.log x ^ (1 - (B : ℝ)) * (Real.log x) ^ 2) := by ring
          _ = _ := by rw [Real.sq_sqrt hx0.le]
      _ ≤ _ := by
        gcongr
        norm_num
  have hlong :
      6 * liuPanPerronHalfStep x ^ panSourceSigma x *
          (panLongConstant * (Real.log x) ^ 2 / Real.log x ^ (B : ℝ)) * Real.log (1 + panSourceHeight x) ≤
        (36 * Real.exp 2 * panLongConstant) * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) := by
    calc
      _ ≤ 6 * (2 * Real.exp 2 * (x : ℝ)) *
          (panLongConstant * (Real.log x) ^ 2 / Real.log x ^ (B : ℝ)) * (3 * (Real.log x) ^ 2) := by
        gcongr
        exact halfStep_source_power_le_linear hxlog hxpos le_rfl
      _ = _ := by
        rw [Real.rpow_sub hlogpos, Real.rpow_ofNat]
        ring
  refine hmain.trans (add_le_add (add_le_add hshort hlong) le_rfl |>.trans ?_)
  exact le_of_eq (by unfold panCellConstant; ring)


theorem numerical_high_source_depth_saving (B x : ℕ) (hx : GRHQuarterChen.targetCutoff≤ x) (hBcap : B≤38)
    (m A₁ A₂ : ℕ) (f : ℕ → ℂ) (hAx : A₂ ≤ x)
    (hApower : (A₂ : ℝ) ≤ (x : ℝ)^(2/3 : ℝ))
    (hAlow : Real.log (x : ℝ)^((2 : ℝ)*B) ≤ A₁) (hf : ∀ n, ‖f n‖ ≤ 1) :
    panIymHigh (panSourceG f m) (panSourceD m) x A₁ A₂
      ⌊lowConductor x (B : ℝ)⌋₊ ⌊upperConductor x (B : ℝ)⌋₊ ≤
    (Nat.log 2 x + 1 : ℝ)^2 *
      (panCellConstant*x*Real.log x^(4-(B : ℝ)) + 776/(x : ℝ)) := by
  have hxlog := numerical_high_log_four hx
  have hC : 0 < panCellConstant := by
    unfold panCellConstant panShortConstant panLongConstant
    have := panSharpConstant_pos
    positivity
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hxlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hA₁ : 0 < A₁ := by
    have hp : (0 : ℝ) < Real.log x ^ ((2 : ℝ) * B) :=
      Real.rpow_pos_of_pos (by linarith only [hxlog]) _
    have : (0 : ℝ) < A₁ := hp.trans_le hAlow
    exact_mod_cast this
  let M := panCellConstant * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) + 776 / (x : ℝ)
  have hM : 0 ≤ M := by
    dsimp [M]
    have : 0 ≤ Real.log (x : ℝ) := by linarith
    positivity
  let s := (range (Nat.log 2 x + 1)).filter
    (fun j => conductorRadius x (B : ℝ) j ≤ upperConductor x (B : ℝ))
  have hs : s.card ≤ Nat.log 2 x + 1 :=
    (card_filter_le _ _).trans_eq (card_range _)
  calc
    _ ≤ ∑ j ∈ s, ∑ k ∈ range (panDyadicDepth A₁ A₂),
        sourceCell f m x A₁ A₂ k (conductorRadius x (B : ℝ) j) :=
      panIymHigh_le_sum_active_sourceCells f m x A₁ A₂ B hxlog1 hB hA₁
    _ ≤ ∑ j ∈ s, ∑ _k ∈ range (panDyadicDepth A₁ A₂), M := by
      apply sum_le_sum
      intro j hj
      apply sum_le_sum
      intro k hk
      exact numerical_source_cell_log_saving B x hx hBcap j m A₁ A₂ k f hAx
        (mem_filter.mp hj).2 hApower hAlow hf
    _ = (s.card : ℝ) * (panDyadicDepth A₁ A₂ : ℝ) * M := by simp; ring
    _ ≤ (Nat.log 2 x + 1 : ℝ) * (Nat.log 2 x + 1 : ℝ) * M := by
      gcongr
      · exact_mod_cast hs
      · exact_mod_cast source_depth_le (A₁ := A₁) hAx
    _ = _ := by rw [pow_two]



theorem numerical_high_source_log_saving (B x : ℕ) (hx : GRHQuarterChen.targetCutoff≤ x) (hBcap : B≤38)
    (m A₁ A₂ : ℕ) (f : ℕ → ℂ) (hAx : A₂ ≤ x)
    (hApower : (A₂ : ℝ) ≤ (x : ℝ)^(2/3 : ℝ))
    (hAlow : Real.log (x : ℝ)^((2 : ℝ)*B) ≤ A₁) (hf : ∀ n, ‖f n‖ ≤ 1) :
    panIymHigh (panSourceG f m) (panSourceD m) x A₁ A₂
      ⌊lowConductor x (B : ℝ)⌋₊ ⌊upperConductor x (B : ℝ)⌋₊ ≤
    panHighConstant*x*Real.log x^(6-(B : ℝ)) + 6984*Real.log x^2/(x : ℝ) := by
  have hxlog := numerical_high_log_four hx
  have hC : 0 < panCellConstant := by
    unfold panCellConstant panShortConstant panLongConstant
    have := panSharpConstant_pos
    positivity
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  calc
    _ ≤ (Nat.log 2 x + 1 : ℝ) ^ 2 *
        (panCellConstant * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) + 776 / (x : ℝ)) :=
      numerical_high_source_depth_saving B x hx hBcap m A₁ A₂ f hAx hApower hAlow hf
    _ ≤ (3 * Real.log x) ^ 2 *
        (panCellConstant * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) + 776 / (x : ℝ)) := by
      gcongr
      exact log_depth_le_three_log hxlog
    _ = _ := by
      rw [show (6 - (B : ℝ) : ℝ) = 2 + (4 - (B : ℝ)) by ring, Real.rpow_add hlogpos,
        Real.rpow_two]
      unfold panHighConstant
      ring


theorem numerical_pan_conductor_bounds (B N : ℕ) (hN : GRHQuarterChen.targetCutoff≤ N) (hB : B≤38) :
    1 ≤ Real.log (N : ℝ) ∧ 1 ≤ ⌊lowConductor N (B : ℝ)⌋₊ ∧
      ⌊lowConductor N (B : ℝ)⌋₊ ≤ panModulusCutoff N (B : ℝ) ∧
      (panModulusCutoff N (B : ℝ) : ℝ) ≤ Real.sqrt N ∧
      panModulusCutoff N (B : ℝ) ≤ N := by
  have hl := numerical_high_log_four hN
  have hlog : 1 ≤ Real.log (N : ℝ) := by linarith only [hl]
  have hN9 := GRHQuarterChen.target_nine_le hN
  have hbound := GRHQuarterChen.log_power_at_target hN (k:=2*B) (by omega) (δ:=1/2) (by norm_num)
  have hd : 1 ≤ lowConductor N (B : ℝ) := lowConductor_ge_one hlog (Nat.cast_nonneg B)
  have hdp : 0 < lowConductor N (B : ℝ) := zero_lt_one.trans_le hd
  have hsq : lowConductor N (B : ℝ)*lowConductor N (B : ℝ) ≤ Real.sqrt N := by
    rw [lowConductor, Real.rpow_natCast, ← pow_two, ← pow_mul, Nat.mul_comm B 2,
      Real.sqrt_eq_rpow]
    exact hbound
  have horder : lowConductor N (B : ℝ) ≤ upperConductor N (B : ℝ) :=
    (le_div_iff₀ hdp).mpr hsq
  have hfloor : (panModulusCutoff N (B : ℝ) : ℝ) ≤ Real.sqrt N := by
    rw [panModulusCutoff_eq_upper]
    exact (Nat.floor_le (by unfold upperConductor; positivity)).trans
      (upperConductor_le_sqrt hlog (Nat.cast_nonneg B))
  refine ⟨hlog, Nat.le_floor (by simpa using hd), ?_, hfloor, ?_⟩
  · rw [panModulusCutoff_eq_upper]
    exact Nat.floor_mono horder
  · exact_mod_cast hfloor.trans (Real.sqrt_le_self_iff.mpr
      (Or.inr (by exact_mod_cast (show 1 ≤ N by omega))))

theorem numerical_pan_budget (U b N : ℕ) (hN : GRHQuarterChen.targetCutoff≤ N) (hUb : U+b+1≤99)
    (K : ℝ) (hK : 0 ≤ K) (m A₂ Q : ℕ)
    (hm : 1 ≤ m) (hmN : (m : ℝ) ≤ Real.sqrt N)
    (hA : (A₂ : ℝ) ≤ (N : ℝ)^(2/3 : ℝ))
    (hQ : (Q : ℝ) ≤ Real.log (N : ℝ)^b) :
    (Q : ℝ)*((K*N/Real.log (N : ℝ)^(U+b+2))*(1+Real.log N)+
      (A₂ : ℝ)*(m.primeFactors.card : ℝ)) ≤
        (2*K+2)*N/Real.log (N : ℝ)^U := by
  have hN9 := GRHQuarterChen.target_nine_le hN
  have hL : 1 ≤ Real.log (N : ℝ) := log_one_le_of_eight_le (by omega)
  have hlog := GRHQuarterChen.log_power_at_target hN (k:=U+b+1) (by omega) (δ:=1/3) (by norm_num)
  have hlog' : Real.log (N : ℝ)^((U : ℝ)+(b : ℝ)+1) ≤ (N : ℝ)^(1/3 : ℝ) := by
    rw [show (U : ℝ)+(b : ℝ)+1 = ((U+b+1 : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_natCast]
    exact hlog
  have hmX : (m : ℝ) ≤ N := hmN.trans
    (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1 ≤ N by omega))))
  have hcard := PanLow.primeFactors_card_le_log_of_le (by omega : 0 < m) hmX
  have htwo : (Real.log 2)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀' (Real.log_pos (by norm_num))]
    linarith [Real.log_two_gt_d9]
  have hW : (m.primeFactors.card : ℝ) ≤ 2*Real.log (N : ℝ) :=
    hcard.trans (mul_le_mul_of_nonneg_right htwo (zero_le_one.trans hL))
  have hh := PanLow.low_budget_scalar
    (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega)) hL
    (Nat.cast_nonneg A₂) (Nat.cast_nonneg m.primeFactors.card) (Nat.cast_nonneg Q)
    hK (by norm_num : (0 : ℝ) ≤ 2) hA hW
    (show (Q : ℝ) ≤ Real.log (N : ℝ)^(b : ℝ) by simpa only [Real.rpow_natCast] using hQ) hlog'
  simpa only [show (U : ℝ)+(b : ℝ)+2 = ((U+b+2 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast] using hh


end ChenEffective.GRHQuarterChen.High
end

/- Strong moving input, proved independently for log N >= 10000. -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LiuWeight AnalyticNumberTheory.LargeSieve
theorem pan_log_log_cap {L : ℝ} (hL : (130690:ℝ)≤ L) : log L≤ L/10880 := GRHQuarterChenBudget.pan_log_log_cap hL

theorem pan_prime_moving {N : ℕ} (hN : targetCutoff≤ N) {b s : ℕ}
    (hb : b≤40) (hs : s≤72) (a : ℕ) (ha : 1≤ a)
    (haN : (a:ℝ)≤(N:ℝ)^(2/3:ℝ)) (q : ℕ) (hq2 : 2≤ q)
    (hq : (q:ℝ)≤ Real.log (N:ℝ)^b) (χ : PrimitiveCharacter q) (hχ : χ.1≠1) :
    ‖PanLow.primePrefix χ.1 (N/a)‖≤((N:ℝ)/Real.log (N:ℝ)^s)/(a:ℝ) :=
  GRHStrongMoving.pan_prime_moving (by linarith only [target_log_lower hN]) hb hs a ha haN q hq2 hq χ hχ

theorem pan_principal_moving {N : ℕ} (hN : targetCutoff≤ N) {s : ℕ}
    (hs : s≤70) (a : ℕ) (ha : 1≤ a) (haN : (a:ℝ)≤(N:ℝ)^(2/3:ℝ)) :
    |PanPrincipal.primeCount (N/a)-liuLogarithmicIntegral (2/Real.log 2) ((N:ℝ)/a)|≤
      ((N:ℝ)/Real.log (N:ℝ)^s)/(a:ℝ) :=
  GRHStrongMoving.pan_principal_moving (by linarith only [target_log_lower hN]) hs a ha haN
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenPanEndpoints -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Complex Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem pan_log_cutoff_at_target {k N : ℕ} (hk : k≤34) (hN : targetCutoff≤ N) :
    logPowerCutoff k≤ N := by
  apply le_trans _ hN
  rw [targetCutoff_eq]
  unfold logPowerCutoff
  apply Nat.pow_le_pow_right (by norm_num)
  have hh := Nat.pow_le_pow_left (by omega : k+1≤35) 2
  nlinarith only [hh]

theorem pan_low_at_target (U b N : ℕ) (hN : targetCutoff≤ N)
    (hU : U≤32) (hb : b≤38)
    (m A₁ A₂ Q : ℕ) (g : ℕ→ℂ) (hm : 1≤ m) (hmN : (m:ℝ)≤ Real.sqrt N)
    (hA : (A₂:ℝ)≤(N:ℝ)^(2/3:ℝ)) (hQ : (Q:ℝ)≤ Real.log (N:ℝ)^b)
    (hg : ∀ a∈Ioc A₁ A₂, ‖g a‖≤1) :
    PanLow.nonprincipalLow g (fun n => if n.Prime ∧ n.Coprime m then 1 else 0)
      N A₁ A₂ Q≤4*N/Real.log (N:ℝ)^U :=
  GRHStrongMoving.pan_low_of_log U b N (by linarith only [target_log_lower hN]) hU hb m A₁ A₂ Q g hm hmN hA hQ hg

theorem pan_principal_at_target (s N : ℕ) (hN : targetCutoff≤ N) (hs : s≤32)
    (q A₁ A₂ : ℕ) (hq : 1≤ q) (hqN : (q:ℝ)≤ Real.sqrt N)
    (hA : (A₂:ℝ)≤(N:ℝ)^(2/3:ℝ)) :
    |PanPrincipal.principalError N A₁ A₂ q|≤4*N/Real.log (N:ℝ)^s :=
  GRHStrongMoving.pan_principal_of_log s N (by linarith only [target_log_lower hN]) hs q A₁ A₂ hq hqN hA

theorem pan_actual_paid_principal (s N : ℕ) (hN : targetCutoff≤ N) (hs : s≤32)
    (B : ℝ) (q : ℕ) (hq : 1≤ q) (hqN : (q:ℝ)≤ Real.sqrt N) :
    liuPanActualError (2/Real.log 2) N B q ≤
      (liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N B)
        (liuPanSourceIntervalUpper N) q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))+
        4*N/Real.log (N:ℝ)^s)/q.totient := by
  have hp := pan_principal_at_target s N hN hs q
    (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) hq hqN
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  rw [principalError_eq_liuPanActualPrincipalRaw] at hp
  exact (liuWeight_intervalMaxL_le_nonprincipal_add_principal (2/Real.log 2)
    N (liuSourceZ10 N) (liuSourceY3 N) _ _ q hq).trans
      (div_le_div_of_nonneg_right (add_le_add le_rfl hp) (Nat.cast_nonneg _))

#print axioms pan_low_at_target
#print axioms pan_principal_at_target
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenPanLedger -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def panLedgerConstant (_U : ℕ) : ℝ := 4+panHighConstant+6984
def panPrincipalConstant (_s : ℕ) : ℝ := 4
theorem panLedgerConstant_pos (U : ℕ) : 0<panLedgerConstant U := by
  unfold panLedgerConstant panHighConstant panCellConstant panShortConstant panLongConstant
  have := panSharpConstant_pos
  positivity
theorem panPrincipalConstant_pos (s : ℕ) : 0<panPrincipalConstant s := by norm_num [panPrincipalConstant]
theorem numerical_pan_ledger (U N : ℕ) (hN : targetCutoff ≤ N) (hU : U≤32)
    (m : ℕ) (hm : m ∈ Icc 1 (panModulusCutoff N ((U+6 : ℕ) : ℝ))) :
    liuPanPrimitiveCofactorLedger N (liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ))
      (liuPanSourceIntervalUpper N) (panModulusCutoff N ((U+6 : ℕ) : ℝ)) m
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
        panLedgerConstant U*N/Real.log (N : ℝ)^U := by
  have hNR : logPowerCutoff (U+2)≤ N := pan_log_cutoff_at_target (by omega) hN
  obtain ⟨hlog, hD1, hD, hDN, hcut⟩ := High.numerical_pan_conductor_bounds (U+6) N hN (by omega)
  have hN9 := (logPowerCutoff_nine_le _).trans hNR
  obtain ⟨hmpos, hmcutoff⟩ := mem_Icc.mp hm
  have hmN : (m : ℝ) ≤ Real.sqrt N :=
    (show (m : ℝ) ≤ panModulusCutoff N ((U+6 : ℕ) : ℝ) by exact_mod_cast hmcutoff).trans hDN
  have hA : (liuPanSourceIntervalUpper N : ℝ) ≤ (N : ℝ)^(2/3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hAN : liuPanSourceIntervalUpper N ≤ N := by
    exact_mod_cast hA.trans (Real.rpow_le_self_of_one_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num))
  have hf : ∀ a, ‖(liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)‖ ≤ 1 := by
    intro a
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_liuWeight] using
      liuWeight_le_one N (liuSourceZ10 N) (liuSourceY3 N) a
  have hlow := pan_low_at_target U (U+6) N hN hU (by omega) m
    (liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ)) (liuPanSourceIntervalUpper N)
    ⌊lowConductor N ((U+6 : ℕ) : ℝ)⌋₊
    (panSourceG (fun a => (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)) m)
    hmpos hmN hA (by
      have hl0 : 0 ≤ Real.log (N : ℝ) := by linarith only [hlog]
      simpa only [lowConductor, Real.rpow_natCast] using
        (Nat.floor_le (Real.rpow_nonneg hl0 ((U+6 : ℕ) : ℝ)))) (by
      intro a _
      unfold panSourceG
      split_ifs
      · exact hf a
      · simp)
  have hhigh := High.numerical_high_source_log_saving (U+6) N hN (by omega) m
    (liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ)) (liuPanSourceIntervalUpper N)
    (fun a => (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)) hAN hA
    (log_rpow_lt_liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ)).le hf
  have he : 6-((U+6 : ℕ) : ℝ) = -(U : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg (show 0 ≤ Real.log (N : ℝ) by linarith only [hlog]),
    Real.rpow_natCast, ← div_eq_mul_inv] at hhigh
  have hDfun : panSourceD m = (fun n => if n.Prime ∧ n.Coprime m then (1 : ℂ) else 0) := by
    funext n
    simp only [panSourceD, and_comm]
  rw [liuPanPrimitiveCofactorLedger_eq_source,
    PanLow.nonprincipalLow_eq_low_add_high _ _ _ _ _ _ _ hD1 hD,
    panModulusCutoff_eq_upper]
  rw [← hDfun] at hlow
  have hr := H30.numerical_pan_high_remainder U N hNR
  calc
    _ ≤ 4*N/Real.log (N : ℝ)^U +
        (panHighConstant*N/Real.log (N : ℝ)^U + 6984*Real.log (N : ℝ)^2/N) :=
      add_le_add hlow hhigh
    _ ≤ 4*N/Real.log (N : ℝ)^U +
        (panHighConstant*N/Real.log (N : ℝ)^U + 6984*N/Real.log (N : ℝ)^U) := by
      exact add_le_add le_rfl (add_le_add le_rfl hr)
    _ = _ := by unfold panLedgerConstant; ring


#print axioms numerical_pan_ledger
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenPanUnweighted -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
def panUnweightedConstant (A : ℕ) : ℝ := 4*(panLedgerConstant (A+2)+panPrincipalConstant (A+2))
theorem panUnweightedConstant_pos (A : ℕ) : 0 < panUnweightedConstant A := by
  unfold panUnweightedConstant
  have := panLedgerConstant_pos (A+2)
  have := panPrincipalConstant_pos (A+2)
  positivity

theorem numerical_pan_unweighted (A N : ℕ) (hN : targetCutoff ≤ N) (hA : A≤30) :
    liuPanUnweightedTheorem2Sum (2/Real.log 2) N ((A+8 : ℕ) : ℝ) ≤
      panUnweightedConstant A*N/Real.log (N : ℝ)^(A : ℝ) := by
  have hNk := hN
  have hNp := hN
  obtain ⟨hlog, _, _, hDroot, hDN⟩ := High.numerical_pan_conductor_bounds (A+8) N hN (by omega)
  let K := panLedgerConstant (A+2)
  let P := panPrincipalConstant (A+2)
  have hK : 0 < K := panLedgerConstant_pos _
  have hP : 0 < P := panPrincipalConstant_pos _
  have hpaid := pan_actual_paid_principal (A+2) N hNp (by omega)
  let D := panModulusCutoff N ((A+8 : ℕ) : ℝ)
  let M := K * N / Real.log (N : ℝ) ^ (((A+2 : ℕ) : ℝ))
  let T := P * N / Real.log (N : ℝ) ^ (((A+2 : ℕ) : ℝ))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hmass := liuPanActualNonprincipal_sum_le_log_sq N (liuPanSourceIntervalLower N ((A+8 : ℕ) : ℝ))
    (liuPanSourceIntervalUpper N) D (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
    M hM hDN (by
      simpa only [M, K, D, Real.rpow_natCast, Nat.add_assoc, Nat.reduceAdd] using
        numerical_pan_ledger (A+2) N hNk (by omega))
  have hprincipal : T * ∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ ≤
      T * (1 + Real.log (N : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_left (PanCofactor.reciprocal_totient_mass_le_log_sq hDN) hT
  calc
    _ ≤ ∑ q ∈ Icc 1 D, liuPanActualError (2 / Real.log 2) N ((A+8 : ℕ) : ℝ) q :=
      liuPanUnweightedTheorem2Sum_le_closed _ _ _
    _ ≤ ∑ q ∈ Icc 1 D,
        (liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N ((A+8 : ℕ) : ℝ))
          (liuPanSourceIntervalUpper N) q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) + T) /
            q.totient := by
      apply sum_le_sum
      intro q hq
      simpa only [T, P, panPrincipalConstant, Real.rpow_natCast] using hpaid ((A+8 : ℕ) : ℝ) q (mem_Icc.mp hq).1
        ((by exact_mod_cast (mem_Icc.mp hq).2 : (q : ℝ) ≤ D).trans hDroot)
    _ = (∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ *
        liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N ((A+8 : ℕ) : ℝ))
          (liuPanSourceIntervalUpper N) q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) +
        T * ∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ := by
      simp only [add_div, sum_add_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ M * (1 + Real.log (N : ℝ)) ^ 2 + T * (1 + Real.log (N : ℝ)) ^ 2 :=
      add_le_add hmass hprincipal
    _ = ((K + P) * N / Real.log (N : ℝ) ^ (((A+2 : ℕ) : ℝ))) * (1 + Real.log (N : ℝ)) ^ 2 := by
      dsimp [M, T]
      ring
    _ ≤ _ := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, panUnweightedConstant] using
        pan_log_sq_payment N (A : ℝ) (K + P) (by positivity) hlog


#print axioms numerical_pan_unweighted
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenPanWeighted -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
def panWeightedSaving (A : ℕ) : ℕ := 2*A+20
def panWeightedCutoff (A : ℕ) : ℕ := panWeightedSaving A+8
def panWeightedSquareConstant (A : ℕ) : ℝ :=
  2^20*H30.panActualEnvelopeConstant (2/Real.log 2)*panUnweightedConstant (panWeightedSaving A)
def panWeightedConstant (A : ℕ) : ℝ := Real.sqrt (panWeightedSquareConstant A)+1

theorem numerical_pan_weighted_square (κ : ℝ) (N : ℕ) (B : ℝ)
    (hN : 2 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) (hB : 0 ≤ B) :
    liuPanWangDingCorollary230Sum κ N B^2 ≤
      (1+Real.log (N : ℝ))^20 * (H30.panActualEnvelopeConstant κ*N*
        liuPanUnweightedTheorem2Sum κ N B) := by
  let S := liuPanSquarefreeCarrier N B
  let E := liuPanActualError κ N B
  let X := H30.panActualEnvelopeConstant κ*N*(1+Real.log (N : ℝ))^2
  have hX : 0 ≤ X := by dsimp [X]; positivity [H30.panActualEnvelopeConstant_pos κ]
  have hsq : ∀ q ∈ S, Squarefree q := fun q hq => (mem_filter.mp hq).2
  have hpos : ∀ q ∈ S, 0 < q := fun q hq => Nat.pos_of_ne_zero (hsq q hq).ne_zero
  have hE : ∀ q ∈ S, 0 ≤ E q := fun q _ => liuPanActualError_nonneg κ N B q
  have hSN : S ⊆ Icc 1 N := by
    intro q hq
    exact mem_Icc.mpr ⟨hpos q hq,
      panSourceStrictModulusCutoff_mem_le (by omega) hlog hB (mem_filter.mp hq).1⟩
  have hc := numerical_totient_cauchy S
    (fun q => (3 : ℝ)^q.primeFactors.card) E X hpos hE (by
      intro q hq
      exact H30.numerical_pan_envelope κ N _ _ q hN
        (hpos q hq) (mem_Icc.mp (hSN hq)).2)
  have hm : (∑ q ∈ S, ((3 : ℝ)^q.primeFactors.card)^2/q.totient) ≤
      (1+Real.log (N : ℝ))^18 := by
    calc
      _ = ∑ q ∈ S, (9 : ℝ)^q.primeFactors.card/q.totient := by
        apply sum_congr rfl
        intro q _
        rw [pow_two, ← mul_pow]
        norm_num
      _ ≤ _ := numerical_totient_nine_mass (by omega) S hSN hsq
  have ho : (∑ q ∈ S, E q) ≤ liuPanUnweightedTheorem2Sum κ N B :=
    liuPanSquarefreeErrorSum_le_unweighted κ N B
  rw [liuPanWeightedSum_eq_squarefree]
  calc
    _ ≤ (∑ q ∈ S, ((3 : ℝ)^q.primeFactors.card)^2/q.totient)*(X*∑ q ∈ S, E q) := hc
    _ ≤ (1+Real.log (N : ℝ))^18*(X*liuPanUnweightedTheorem2Sum κ N B) :=
      mul_le_mul hm (mul_le_mul_of_nonneg_left ho hX)
        (mul_nonneg hX (sum_nonneg hE)) (by positivity)
    _ = _ := by dsimp [X]; ring

theorem numerical_pan_weighted (A N : ℕ) (hN : targetCutoff ≤ N) (hA : A≤5) :
    liuPanWangDingCorollary230Sum (2/Real.log 2) N (panWeightedCutoff A : ℝ) ≤
      panWeightedConstant A*N/Real.log (N : ℝ)^A := by
  have hlog : 1≤ Real.log (N:ℝ) := by have := target_log_lower hN; linarith
  have hN2 : 2≤ N := by
    have := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
    omega
  have hl0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hK := panUnweightedConstant_pos (panWeightedSaving A)
  have hsrc := numerical_pan_unweighted (panWeightedSaving A) N
    hN (by unfold panWeightedSaving; omega)
  rw [Real.rpow_natCast] at hsrc
  have hs := numerical_pan_weighted_square (2/Real.log 2) N (panWeightedCutoff A : ℝ)
    hN2 hlog (Nat.cast_nonneg _)
  have henv := H30.panActualEnvelopeConstant_pos (2/Real.log 2)
  have hD : 0 ≤ panWeightedSquareConstant A := by unfold panWeightedSquareConstant; positivity
  have hmajor : liuPanWangDingCorollary230Sum (2/Real.log 2) N (panWeightedCutoff A : ℝ)^2 ≤
      panWeightedSquareConstant A*((N : ℝ)/Real.log (N : ℝ)^A)^2 := by
    calc
      _ ≤ (1+Real.log (N : ℝ))^20*(H30.panActualEnvelopeConstant (2/Real.log 2)*N*
          (panUnweightedConstant (panWeightedSaving A)*N/Real.log (N : ℝ)^(panWeightedSaving A))) :=
        hs.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsrc (by positivity)) (by positivity))
      _ ≤ (2*Real.log (N : ℝ))^20*(H30.panActualEnvelopeConstant (2/Real.log 2)*N*
          (panUnweightedConstant (panWeightedSaving A)*N/Real.log (N : ℝ)^(panWeightedSaving A))) := by
        gcongr
        linarith only [hlog]
      _ = _ := by
        unfold panWeightedSaving panWeightedSquareConstant
        rw [pow_add, pow_mul]
        field_simp [hl0.ne']
        simp only [panWeightedSaving, Nat.mul_comm]
        ring
  have hleft : 0 ≤ liuPanWangDingCorollary230Sum (2/Real.log 2) N (panWeightedCutoff A : ℝ) := by
    unfold liuPanWangDingCorollary230Sum
    exact sum_nonneg fun q _ => mul_nonneg (by positivity) (liuMainPanCoprimeIntervalMaxL_nonneg ..)
  have ht : 0 ≤ panWeightedConstant A*N/Real.log (N : ℝ)^A := by unfold panWeightedConstant; positivity
  have hDs : panWeightedSquareConstant A ≤ panWeightedConstant A^2 := by
    unfold panWeightedConstant
    nlinarith only [Real.sq_sqrt hD, Real.sqrt_nonneg (panWeightedSquareConstant A)]
  apply (sq_le_sq₀ hleft ht).mp
  exact hmajor.trans ((mul_le_mul_of_nonneg_right hDs (sq_nonneg _)).trans_eq (by ring))


#print axioms numerical_pan_weighted
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenPanSource -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LiuWeight
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem pan_log_power_at_target {N : ℕ} (hN : targetCutoff≤ N) {k : ℕ}
    (hk : k≤39) {δ : ℝ} (hδ : (9/2500:ℝ)≤δ) :
    log (N:ℝ)^k≤(N:ℝ)^δ := by
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hn : 0<N := by
    by_contra h
    have hh : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hkR : (k:ℝ)≤39 := by exact_mod_cast hk
  have hh := mul_le_mul_of_nonneg_left (pan_log_log_cap hL) (Nat.cast_nonneg k)
  have hm := mul_le_mul_of_nonneg_right hkR (show 0≤ 29*log (N:ℝ)/500000 by positivity)
  have hd := mul_le_mul_of_nonneg_right hδ hl.le
  rw [Real.rpow_def_of_pos hnR]
  calc
    _ = exp ((k:ℝ)*log (log (N:ℝ))) := by rw [exp_nat_mul (log (log (N:ℝ))) k,exp_log hl]
    _ ≤ _ := exp_le_exp.mpr (by nlinarith only [hh,hm,hd,hl])

theorem pan_source_support_at_target {N : ℕ} (hN : targetCutoff≤ N) :
    liuPanSourceIntervalLower N (38:ℝ)<liuSourceZ10 N := by
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hp := log_power_at_target hN (k:=76) (by norm_num) (δ:=(1/20:ℝ)) (by norm_num)
  have hlarge : 2^20≤ N := by
    have hh := pan_log_cutoff_at_target (k:=1) (by norm_num) hN
    have hc : 2^20≤ logPowerCutoff 1 := by norm_num [logPowerCutoff]
    exact hc.trans hh
  have htwo : (2:ℝ)≤(N:ℝ)^(1/20:ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num : (0:ℝ)≤2) hn.le (by norm_num : (0:ℝ)<20)).mpr
    norm_num
    exact_mod_cast hlarge
  have hs : ((N:ℝ)^(1/20:ℝ))^2=(N:ℝ)^(1/10:ℝ) := by
    rw [← rpow_natCast,← rpow_mul hn.le]
    norm_num
  have hb : log (N:ℝ)^76+2≤(N:ℝ)^(1/10:ℝ) := by nlinarith only [hp,htwo,hs]
  have hh := Nat.floor_mono hb
  have hL := target_log_lower hN
  have hl : 0≤ log (N:ℝ) := by linarith only [hL]
  have hadd : ⌊log (N:ℝ)^76+2⌋₊=⌊log (N:ℝ)^76⌋₊+2 := by
    convert Nat.floor_add_natCast (pow_nonneg hl 76) 2 using 1 <;> norm_num
  rw [hadd] at hh
  unfold liuPanSourceIntervalLower liuSourceZ10
  norm_num only [rpow_ofNat]
  omega

theorem pan_source_level_at_target {N : ℕ} (hN : targetCutoff≤ N) :
    liuSourceDEpsilon N (9/2500:ℝ)≤ panModulusCutoff N (39:ℝ) := by
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hp := pan_log_power_at_target hN (k:=39) (by norm_num) (δ:=(9/2500:ℝ)) (by norm_num)
  unfold liuSourceDEpsilon panModulusCutoff
  apply Nat.floor_mono
  rw [rpow_sub hn]
  norm_num only [rpow_ofNat]
  exact div_le_div_of_nonneg_left (rpow_nonneg hn.le _) (pow_pos hl 39) hp

theorem pan_source_at_target {N : ℕ} (hN : targetCutoff≤ N) :
    LiuPaperQCoprimeRBound (liuLogarithmicIntegral (2/log 2)) N (9/2500:ℝ)
      (5:ℝ) (panWeightedConstant 5) := by
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hL := target_log_lower hN
  have hlog : 1<log (N:ℝ) := by linarith only [hL]
  have hb := numerical_pan_weighted 5 N hN (by norm_num)
  have hc := pan_source_level_at_target hN
  apply liuPaperQCoprimeRBound_of_liuMainPanEndpointMeanValueAt
    (liuLogarithmicIntegral (2/log 2)) N (9/2500:ℝ) (5:ℝ) (39:ℝ)
    (panWeightedConstant 5) hc
  have hh := H30.liuMainPanEndpointWeightedSum_le_corollary230Sum (2/log 2) N
    (38:ℝ) (fun _ _ => liuMainPanCoprimeSum_eq_panSourceInterval _ (by omega)
      (pan_source_support_at_target hN))
    (range_panModulusCutoff_add_one_subset_sourceStrict N (38:ℝ) (by omega) hlog)
  norm_num only [panWeightedCutoff,panWeightedSaving,Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at hb
  unfold LiuMainPanEndpointMeanValueAt
  convert hh.trans hb using 1 <;> norm_num only [rpow_ofNat]

#print axioms pan_source_at_target
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenPanCanonical -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def panDivisorConstant : ℝ := H30.panDivisorConstant
def panNormalizationConstant : ℝ := H30.panNormalizationConstant
def panCanonicalConstant (A : ℕ) : ℝ := panWeightedConstant A+panNormalizationConstant
theorem numerical_pan_full_divisor {N w : ℕ} (hN : mertensProductThreshold 2 ≤ N)
    (hw : w ≤ N) :
    paperQStyleFullDivisorWeightSum N w ≤ panDivisorConstant*Real.log (N : ℝ)^3 := by
  have hprod := numerical_mertens_product (by norm_num : 0 < (2 : ℕ)) hN
  have hNP := (le_max_left _ _).trans hN
  have hN9 := (logPowerCutoff_nine_le _).trans hNP
  have hl0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hP := AnalyticNumberTheory.Mertens.primeProduct_pos N
  have hlow := (abs_le.mp hprod).1
  have hi : (AnalyticNumberTheory.Mertens.primeProduct N)⁻¹ ≤
      2*Real.exp Real.eulerMascheroniConstant*Real.log (N : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hP).mpr
    norm_num only [Nat.cast_ofNat] at hlow
    nlinarith only [hlow]
  have hh := paperQStyleFullDivisorWeightSum_le_primeProduct_inv_cube N w hw
  rw [MertensTheorem.primeProduct_eq_analyticNumberTheory] at hh
  exact hh.trans ((pow_le_pow_left₀ (by positivity) hi 3).trans_eq
    (by unfold panDivisorConstant H30.panDivisorConstant; ring))


theorem numerical_pan_canonical {N : ℕ} (hN : targetCutoff≤ N) :
    LiuPaperQCoprimeRBound (liuLogarithmicIntegral 2) N (9/2500:ℝ)
      (5:ℝ) (panCanonicalConstant 5) := by
  have hm : 0<(500:ℕ) := by norm_num

  have hNM : mertensProductThreshold 2≤ N := by
    unfold mertensProductThreshold
    apply max_le (pan_log_cutoff_at_target (k:=2) (by norm_num) hN)
    exact (by
      unfold logPowerCutoff
      apply Nat.pow_le_pow_right (by norm_num)
      have hh := Nat.sqrt_le_self (6*2)
      omega : 3^(Nat.sqrt (6*2)+2)≤ logPowerCutoff 0).trans
      (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hNP : logPowerCutoff 24≤ N := pan_log_cutoff_at_target (by norm_num) hN
  have hN9 := (logPowerCutoff_nine_le _).trans hNP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hε : 0 ≤ 9/(2500:ℝ) := by positivity
  have hmass := sum_liuWeight_Icc_le_three_mul_rpow_two_thirds N
    (liuSourceZ10 N) (liuSourceY3 N) (by omega)
  have hcut := (paperQSourceCutoff_le_floor_cuberoot N (9/(2500:ℝ)) (by omega) hε).trans
    (liuSourceY3_le N (by omega))
  have hdiv := numerical_pan_full_divisor hNM hcut
  have hmass0 : 0 ≤ ∑ a ∈ Icc 1 N, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a := by
    apply sum_nonneg
    intro a _
    exact liuWeight_nonneg _ _ _ _
  have hfactor : 0 ≤ paperQStyleFullDivisorWeightSum N (paperQSourceCutoff N (9/(2500:ℝ))) := by
    unfold paperQStyleFullDivisorWeightSum
    positivity
  have hnorm := liuPaperQSourceCoprimeDistributionMajorant_li_normalization_le
    2 (2/Real.log 2) N (9/(2500:ℝ))
  have hloss : |2-2/Real.log 2| *
      (∑ a ∈ Icc 1 N, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a)*
      paperQStyleFullDivisorWeightSum N (paperQSourceCutoff N (9/(2500:ℝ))) ≤
        panNormalizationConstant*N/Real.log (N : ℝ)^5 := by
    have hp := log_pow_le_rpow_inv_explicit (k := 5+3) (m := 3)
      (by norm_num) (le_refl _) hNP
    norm_num only [Nat.cast_ofNat] at hp
    have hscale : (N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^3 ≤ N/Real.log (N : ℝ)^5 := by
      apply (le_div_iff₀ (pow_pos hlog 5)).mpr
      calc
        _ = (N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^(5+3) := by rw [pow_add]; ring
        _ ≤ (N : ℝ)^(2/3 : ℝ)*(N : ℝ)^(1/3 : ℝ) := by gcongr
        _ = _ := by rw [← Real.rpow_add hN0]; norm_num
    calc
      _ ≤ |2-2/Real.log 2| *(3*(N : ℝ)^(2/3 : ℝ))*(panDivisorConstant*Real.log (N : ℝ)^3) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmass (abs_nonneg _)) hdiv hfactor
          (by positivity)
      _ = panNormalizationConstant*((N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^3) := by
        unfold panNormalizationConstant H30.panNormalizationConstant panDivisorConstant; ring
      _ ≤ panNormalizationConstant*(N/Real.log (N : ℝ)^5) := by
        apply mul_le_mul_of_nonneg_left hscale
        unfold panNormalizationConstant H30.panNormalizationConstant H30.panDivisorConstant
        positivity
      _ = _ := by ring
  unfold LiuPaperQCoprimeRBound
  norm_num only [Real.rpow_natCast,Real.rpow_ofNat]
  have hsource := pan_source_at_target hN
  unfold LiuPaperQCoprimeRBound at hsource
  norm_num only [Real.rpow_natCast,Real.rpow_ofNat] at hsource
  exact hnorm.trans ((add_le_add hsource hloss).trans_eq (by unfold panCanonicalConstant; ring))


#print axioms numerical_pan_canonical
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenSelbergRemainder -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def selbergRemainderConstant (A : ℕ) : ℝ :=
  panCanonicalConstant A+1920*liuLogarithmicIntegralUpperConstant 2

theorem numerical_selberg_remainder {N : ℕ} (hN : targetCutoff≤ N) (lam : ℕ→ℝ)
    (hlam : LiuSelbergLambdaAdmissible N (9/2500:ℝ) lam) :
    |liuSelbergRemainder (liuLogarithmicIntegral 2) N (9/2500:ℝ) lam| ≤
      selbergRemainderConstant 5*N/Real.log (N:ℝ)^5 := by

  have hN9 := target_nine_le hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL := log_one_le_of_eight_le (by omega : 8 ≤ N)
  have hl0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL
  have hε : 0 ≤ 9/(2500:ℝ) := by positivity
  have hcop := numerical_pan_canonical hN
  unfold LiuPaperQCoprimeRBound at hcop
  norm_num only [Real.rpow_natCast,Real.rpow_ofNat] at hcop
  have hp := log_power_at_target hN (k:=5+6) (by norm_num) (δ:=1/10) (by norm_num)
  norm_num only [Nat.cast_ofNat] at hp
  have hscale : (N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^6 ≤ N/Real.log (N : ℝ)^5 := by
    apply (le_div_iff₀ (pow_pos hl0 5)).mpr
    calc
      _ = (N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^(5+6) := by rw [pow_add]; ring
      _ ≤ (N : ℝ)^(9/10 : ℝ)*(N : ℝ)^(1/10 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hN0]; norm_num
  have hr := H30.numerical_pan_r1 2 N (9/(2500:ℝ)) hN9 hε
  have hpaid : liuPaperQSourceR1Majorant (liuLogarithmicIntegral 2) N (9/(2500:ℝ)) ≤
      1920*liuLogarithmicIntegralUpperConstant 2*N/Real.log (N : ℝ)^5 := by
    have hC := liuLogarithmicIntegralUpperConstant_nonneg 2
    calc
      _ ≤ 30*liuLogarithmicIntegralUpperConstant 2*(N : ℝ)^(9/10 : ℝ)*
          (1+Real.log (N : ℝ))^6 := hr
      _ ≤ 30*liuLogarithmicIntegralUpperConstant 2*(N : ℝ)^(9/10 : ℝ)*
          (2*Real.log (N : ℝ))^6 := by
        gcongr
        linarith only [hL]
      _ = (1920*liuLogarithmicIntegralUpperConstant 2)*
          ((N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^6) := by ring
      _ ≤ (1920*liuLogarithmicIntegralUpperConstant 2)*(N/Real.log (N : ℝ)^5) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by ring
  exact (abs_liuSelbergRemainder_le_fullDistributionMajorant _ N _ lam (by omega) hlam).trans
    ((liuPaperQSourceFullDistributionMajorant_le_coprime_add_r1 _ N _ (by omega) hε).trans
      ((add_le_add hcop hpaid).trans_eq (by unfold selbergRemainderConstant; ring)))


#print axioms numerical_selberg_remainder
end ChenEffective.GRHQuarterChen
end

