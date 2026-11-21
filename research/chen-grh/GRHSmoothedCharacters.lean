import GRHAssumption
import GRHAbsoluteZeroSum

/-!
Full GRH puts the entire nontrivial zero sum on the square-root scale.
Unlike a finite-height estimate, the zero tail here has no term proportional
to x. The coefficient is completely explicit in the existing analytic
constants. This is a smoothed character estimate, not yet an unsmoothed AP
count or an H=14 Chen theorem.
-/
noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Real Topology
open TernaryGoldbach.Explicit
namespace ChenEffective.GRH
set_option maxHeartbeats 3000000

theorem zero_sum_full_GRH {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {T0 : ℝ}
    (hT0 : max (10 * π * |δ|) 50 ≤ T0) (T : ℝ) :
    ‖∑ u ∈ zerosRect χ T, (multRect χ T u : ℂ) * (Gr u δ 0 * (x : ℂ) ^ u)‖ ≤
      √x * (E0b q + E1b q T0 + E2b q T0 δ) := by
  have hx0 : 0 < x := by linarith
  have habs := absolute_zero_sum_finite_RH hχ hχ1 δ
    (x := 1) (by norm_num) hT0
    (fun ρ hz h0 h1 _ => dirichlet_zeros_on_line q χ ρ h0 h1 hz) T
  simp only [Real.one_rpow, mul_one, Real.sqrt_one, one_mul] at habs
  have hterm (u : ℂ) (hu : u ∈ zerosRect χ T) :
      (multRect χ T u : ℝ) * (‖Gr u δ 0‖ * x ^ u.re) ≤
        √x * ((multRect χ T u : ℝ) * ‖Gr u δ 0‖) := by
    obtain ⟨hL, _, hc⟩ := zerosRect_cases hχ hχ1 hu
    have hp : x ^ u.re ≤ √x := by
      rcases hc with hzero | hstrip
      · rw [hzero, Complex.zero_re, Real.rpow_zero]
        exact Real.one_le_sqrt.mpr hx
      · rw [dirichlet_zeros_on_line q χ u hstrip.1 hstrip.2 hL,
          ← Real.sqrt_eq_rpow]
    calc
      _ ≤ (multRect χ T u : ℝ) * (‖Gr u δ 0‖ * √x) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ u ∈ zerosRect χ T, (multRect χ T u : ℝ) * (‖Gr u δ 0‖ * x ^ u.re) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_cpow_x hx0]
    _ ≤ ∑ u ∈ zerosRect χ T, √x * ((multRect χ T u : ℝ) * ‖Gr u δ 0‖) :=
      Finset.sum_le_sum hterm
    _ = √x * ∑ u ∈ zerosRect χ T, (multRect χ T u : ℝ) * ‖Gr u δ 0‖ := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left habs (Real.sqrt_nonneg x)

theorem smoothed_character_full_GRH {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {T0 : ℝ}
    (hT0 : max (10 * π * |δ|) 50 ≤ T0) :
    ‖Ssum χ δ x‖ ≤ √x * (E0b q + E1b q T0 + E2b q T0 δ) +
      x ^ (-(1 / 2) : ℝ) * Vb q δ / (2 * π) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨Tk, _, hlim⟩ := explicit_formula hχ hχ1 δ hx0
  set I0 := ∫ y : ℝ, hInt χ δ x (((-1 / 2 : ℝ) : ℂ) + y * I)
  have h1 : ‖-Ssum χ δ x - (1 / (2 * π) : ℂ) * I0‖ ≤
      √x * (E0b q + E1b q T0 + E2b q T0 δ) :=
    le_of_tendsto' ((continuous_norm.tendsto _).comp hlim) fun k =>
      zero_sum_full_GRH hχ hχ1 δ hx hT0 (Tk k)
  have h2 : ‖(1 / (2 * π) : ℂ) * I0‖ ≤
      x ^ (-(1 / 2) : ℝ) * Vb q δ / (2 * π) := by
    rw [norm_mul]
    have : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [this, div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (norm_integral_hInt_le hχ hχ1 δ hx0) (by positivity)
  have e : Ssum χ δ x =
      -((-Ssum χ δ x - (1 / (2 * π) : ℂ) * I0) + (1 / (2 * π) : ℂ) * I0) := by ring
  rw [e, norm_neg]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

def gaussianCharacterConstant (q : ℕ) : ℝ :=
  E0b q + E1b q 50 + E2b q 50 0 + Vb q 0 / (2 * π)

theorem gaussian_character_sqrt {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖Ssum χ 0 x‖ ≤ gaussianCharacterConstant q * √x := by
  have h := smoothed_character_full_GRH hχ hχ1 0 hx
    (T0 := 50) (by norm_num)
  have hV : 0 ≤ Vb q 0 / (2 * π) := by
    unfold Vb
    have := DN_nonneg q
    have := thetaD_pos 0
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hp : x ^ (-(1 / 2) : ℝ) ≤ √x := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  calc
    _ ≤ √x * (E0b q + E1b q 50 + E2b q 50 0) +
        x ^ (-(1 / 2) : ℝ) * Vb q 0 / (2 * π) := h
    _ ≤ √x * (E0b q + E1b q 50 + E2b q 50 0) + √x * (Vb q 0 / (2 * π)) := by
      rw [mul_div_assoc]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hp hV)
    _ = _ := by unfold gaussianCharacterConstant; ring

#print axioms zero_sum_full_GRH
#print axioms gaussian_character_sqrt
end ChenEffective.GRH
