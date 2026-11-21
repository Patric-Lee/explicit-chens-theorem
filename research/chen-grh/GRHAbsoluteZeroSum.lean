import TernaryGoldbach.Explicit.ExplicitBound

/-!
The absolute-value form of the existing zero-sum proof. Adapted from the
checked calr3 port, ZeroSumBound.zero_sum_bound (Apache-2.0; repository
LICENSE and the source notices in research/chen-platt). The original proof
already bounds the sum of norms; this lemma exposes that stronger result.
It is generic over a finite-height RH premise, with no external axiom.
-/
noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Real Topology
open TernaryGoldbach.Explicit
namespace ChenEffective.GRH
set_option maxHeartbeats 3000000
theorem absolute_zero_sum_finite_RH {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {T0 : ℝ} (hT0 : max (10 * π * |δ|) 50 ≤ T0)
    (hG : ∀ ρ : ℂ, χ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2) (T : ℝ) :
    ∑ u ∈ zerosRect χ T, (multRect χ T u : ℝ) * (‖Gr u δ 0‖ * x ^ u.re) ≤
      E0b N + √x * E1b N T0 + x * E2b N T0 δ := by
  set Z := zerosRect χ T with hZ
  set m : ℂ → ℝ := fun u => (multRect χ T u : ℝ) with hmdef
  have hm : ∀ u, 0 ≤ m u := fun u => Nat.cast_nonneg _
  have hx0 : 0 < x := by linarith
  have h50 : 50 ≤ T0 := (le_max_right _ _).trans hT0
  have hT00 : 0 < T0 := by linarith
  change (∑ u ∈ Z, m u * (‖Gr u δ 0‖ * x ^ u.re)) ≤
    E0b N + √x * E1b N T0 + x * E2b N T0 δ
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun u => u = 0),
    ← Finset.sum_filter_add_sum_filter_not (Z.filter fun u => ¬ u = 0) (fun u => |u.im| ≤ T0)]
  have hcases : ∀ u ∈ Z.filter (fun u => ¬ u = 0), χ.LFunction u = 0 ∧ 0 < u.re ∧ u.re < 1 := by
    intro u hu
    obtain ⟨huZ, hu0⟩ := Finset.mem_filter.1 hu
    obtain ⟨hL, -, hc⟩ := zerosRect_cases hχ hχ1 huZ
    rcases hc with h | h
    · exact absurd h hu0
    · exact ⟨hL, h⟩
  -- the zero at `0`
  have hA : ∑ u ∈ Z.filter (fun u => u = 0), m u * (‖Gr u δ 0‖ * x ^ u.re) ≤ E0b N := by
    have hcount := sum_multRect_le hχ hχ1 (Z.filter fun u => u = 0) (Finset.filter_subset _ _) 0
      (r := 3) (by norm_num) (by norm_num) (fun u hu => by
        rw [(Finset.mem_filter.1 hu).2]; norm_num)
    have hG0 : ‖Gr 0 δ 0‖ ≤ 112 := by
      have := norm_G_uniform 0 δ (by simp) (by simp)
      simpa using this
    have hpt : ∀ u ∈ Z.filter (fun u => u = 0), m u * (‖Gr u δ 0‖ * x ^ u.re) ≤ m u * 112 := by
      intro u hu
      rw [(Finset.mem_filter.1 hu).2, Complex.zero_re, Real.rpow_zero, mul_one]
      exact mul_le_mul_of_nonneg_left hG0 (hm 0)
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.sum_mul]
    unfold E0b
    have : ∑ u ∈ Z.filter (fun u => u = 0), m u ≤ Real.log (BP N 0 / 0.355) / Real.log (10 / 3) := hcount
    nlinarith
  -- zeros on the critical line, `|γ| ≤ T₀`
  have hB : ∑ u ∈ (Z.filter fun u => ¬ u = 0).filter (fun u => |u.im| ≤ T0),
      m u * (‖Gr u δ 0‖ * x ^ u.re) ≤ √x * E1b N T0 := by
    set S := (Z.filter fun u => ¬ u = 0).filter (fun u => |u.im| ≤ T0) with hS
    have hSZ : S ⊆ Z := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hre : ∀ u ∈ S, u.re = 1 / 2 := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
      obtain ⟨hL, hr1, hr2⟩ := hcases u hu1
      exact hG u hL hr1 hr2 hu2
    have him : ∀ u ∈ S, |u.im| ≤ T0 := fun u hu => (Finset.mem_filter.1 hu).2
    have heq : ∀ u ∈ S, m u * (‖Gr u δ 0‖ * x ^ u.re) = √x * (m u * ‖fline δ u.im‖) := by
      intro u hu
      have hu' : u = ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * I := by
        apply Complex.ext <;> simp [hre u hu]
      rw [hre u hu, ← Real.sqrt_eq_rpow, fline, ← hu']; ring
    rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    exact sum_window_fline_le m (fun u _ => hm u) (h := 3.48) (by norm_num) hT00.le (Jl T0)
      (lt_Jl hT00.le) him (ZL_nonneg N T0)
      (fun k => count_line_window hχ hχ1 hT00.le S hSZ hre him k) δ
  -- zeros above `T₀`
  have hC : ∑ u ∈ (Z.filter fun u => ¬ u = 0).filter (fun u => ¬ |u.im| ≤ T0),
      m u * (‖Gr u δ 0‖ * x ^ u.re) ≤ x * E2b N T0 δ := by
    set S := (Z.filter fun u => ¬ u = 0).filter (fun u => ¬ |u.im| ≤ T0) with hS
    have hSZ : S ⊆ Z := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hre : ∀ u ∈ S, 0 < u.re ∧ u.re < 1 := fun u hu => (hcases u (Finset.mem_filter.1 hu).1).2
    have him : ∀ u ∈ S, T0 < |u.im| := fun u hu => not_le.1 (Finset.mem_filter.1 hu).2
    set idx : ℂ → ℕ := fun u => ⌊(|u.im| - T0) / 4.4⌋₊ with hidx
    have hidxle : ∀ u ∈ S, (idx u : ℝ) * 4.4 ≤ |u.im| - T0 := by
      intro u hu
      have h0 : 0 ≤ (|u.im| - T0) / 4.4 := div_nonneg (by linarith [him u hu]) (by norm_num)
      have := Nat.floor_le h0
      rwa [le_div_iff₀ (by norm_num)] at this
    have hpt : ∀ u ∈ S, m u * (‖Gr u δ 0‖ * x ^ u.re) ≤
        x * (m u * (EB T0 * rhoB ^ idx u) + m u * (EA T0 δ * rhoA δ ^ idx u)) := by
      intro u hu
      obtain ⟨hr1, hr2⟩ := hre u hu
      have hτ := him u hu
      have hGt := norm_G_tail u δ (by linarith) hr2.le hT0 hτ.le
      have hB' : Real.exp (-0.1398 * (|u.im| - T0)) ≤ rhoB ^ idx u := by
        unfold rhoB; rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.2
        nlinarith [hidxle u hu]
      have hA' : EA T0 δ * Real.exp (-1.93 * ((|u.im| - T0) / (π * |δ|))) ≤
          EA T0 δ * rhoA δ ^ idx u := by
        by_cases hδ : δ = 0
        · unfold EA; simp [hδ]
        · refine mul_le_mul_of_nonneg_left ?_ (EA_nonneg T0 δ)
          unfold rhoA; rw [← Real.exp_nat_mul]
          apply Real.exp_le_exp.2
          have hδ0 : 0 < |δ| := abs_pos.2 hδ
          have hP : 0 < π * |δ| := by positivity
          have h1 : (idx u : ℝ) * 4.4 / (π * (|δ| + 1)) ≤ (|u.im| - T0) / (π * |δ|) := by
            calc (idx u : ℝ) * 4.4 / (π * (|δ| + 1)) ≤ (idx u : ℝ) * 4.4 / (π * |δ|) := by
                  apply div_le_div_of_nonneg_left (by positivity) hP; nlinarith [Real.pi_pos]
              _ ≤ _ := div_le_div_of_nonneg_right (hidxle u hu) hP.le
          have e : (idx u : ℝ) * -(1.93 * 4.4 / (π * (|δ| + 1))) =
              -1.93 * ((idx u : ℝ) * 4.4 / (π * (|δ| + 1))) := by ring
          rw [e]; nlinarith
      have hGb : ‖Gr u δ 0‖ ≤ EB T0 * rhoB ^ idx u + EA T0 δ * rhoA δ ^ idx u := by
        have := mul_le_mul_of_nonneg_left hB' (EB_nonneg hT00.le)
        linarith
      have hxr : x ^ u.re ≤ x := by
        calc x ^ u.re ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx hr2.le
          _ = x := Real.rpow_one x
      have hGn := norm_nonneg (Gr u δ 0)
      calc m u * (‖Gr u δ 0‖ * x ^ u.re) ≤ m u * ((EB T0 * rhoB ^ idx u + EA T0 δ * rhoA δ ^ idx u) * x) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hGb hxr (Real.rpow_nonneg hx0.le _) (hGn.trans hGb)) (hm u)
        _ = _ := by ring
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hx0.le
    rw [Finset.sum_add_distrib]
    have hZw : ∀ k : ℕ, ∑ u ∈ S.filter (fun u => idx u = k), m u ≤ 2 * Z3 N T0 + 2 * c3 T0 * (k + 1) :=
      fun k => count_tail_window hχ hχ1 hT00 S hSZ hre him k
    have hZw' : ∀ k : ℕ, ∑ u ∈ S.filter (fun u => idx u = k), m u ≤ 2 * Z3 N T0 + 2 * c3 T0 * (k + 1) :=
      hZw
    have g1 := sum_geom_windows m (fun u _ => hm u) idx (Z0 := 2 * Z3 N T0) (c := 2 * c3 T0)
      (E := EB T0) (ρ := rhoB) (by linarith [Z3_nonneg N T0]) (by linarith [c3_nonneg hT00])
      (EB_nonneg hT00.le) (Real.exp_pos _).le rhoB_lt_one (fun k => by
        have := hZw' k; linarith)
    have g2 := sum_geom_windows m (fun u _ => hm u) idx (Z0 := 2 * Z3 N T0) (c := 2 * c3 T0)
      (E := EA T0 δ) (ρ := rhoA δ) (by linarith [Z3_nonneg N T0]) (by linarith [c3_nonneg hT00])
      (EA_nonneg T0 δ) (Real.exp_pos _).le (rhoA_lt_one δ) (fun k => by
        have := hZw' k; linarith)
    unfold E2b
    linarith
  linarith

#print axioms absolute_zero_sum_finite_RH
end ChenEffective.GRH
