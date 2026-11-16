import TernaryGoldbach.Explicit.Datum

/-! Residue/contour extension adapted from calr3 TernaryGoldbach.Explicit.Datum,
pin ab016043e852c126492310d8fc44ea7849c381b2; original licenses retained in Calr3.
The proof uses a general decaying strip envelope instead of requiring an
exponential Mellin bound. Polynomial envelopes may now be supplied, once
vertical integrability and horizontal decay are proved. This file does not
assert the Logan-kernel estimates or any new prime bound. -/
noncomputable section
namespace ChenEffective.PlattWindow.ContourDecay
open Complex MeasureTheory Set Filter Metric TernaryGoldbach.Explicit
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem rect_identity_of_mellin_diff {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) {φ : ℝ → ℂ} (hM : ∀ s : ℂ, -1 < s.re → DifferentiableAt ℂ (mellin φ) s) {x : ℝ} (hx : 0 < x) {T : ℝ}
    (hT : 0 < T)
    (hbot : ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0)
    (htop : ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], f ((σ : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0) :
    rectInt (fun s => logDeriv f s * (mellin φ s * (x : ℂ) ^ s)) (zT T) (wT T) =
      2 * π * I * ∑ u ∈ zerosRectD f T, (multRectD f T u : ℂ) * (mellin φ u * (x : ℂ) ^ u) := by
  have hf : Differentiable ℂ f := hd.diff
  have hf2 : f 2 ≠ 0 :=
    hd.nz_right _ (by norm_num)
  have hR : 0 < RT T := by unfold RT; linarith
  have hrect : [[(zT T).re, (wT T).re]] ×ℂ [[(zT T).im, (wT T).im]] ⊆ Metric.ball 2 (RT T / 2) := by
    intro s hs
    rw [mem_reProdIm, zT_re, wT_re, zT_im, wT_im, Set.uIcc_of_le (by norm_num),
      Set.uIcc_of_le (by linarith)] at hs
    rw [Metric.mem_ball, dist_eq_norm, RT]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero]
    have h1 : |s.re - 2| ≤ 5 / 2 := by rw [abs_le]; constructor <;> linarith [hs.1.1, hs.1.2]
    have h2 : |s.im| ≤ T := by rw [abs_le]; constructor <;> linarith [hs.2.1, hs.2.2]
    linarith
  have hbd : NoZerosOnSides f (zT T) (wT T) := by
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_, fun y _ => ?_, fun y _ => ?_⟩
    · rw [zT_re, wT_re] at hσ; simpa using hbot σ hσ
    · rw [zT_re, wT_re] at hσ; simpa using htop σ hσ
    · exact hd.nz_right _ (by simp; norm_num)
    · exact hd.nz_strip _ (by simp; norm_num) (by simp; norm_num)
  set U : Set ℂ := {s | -1 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsubU : [[(zT T).re, (wT T).re]] ×ℂ [[(zT T).im, (wT T).im]] ⊆ U := by
    intro s hs
    rw [mem_reProdIm, zT_re, wT_re, Set.uIcc_of_le (by norm_num)] at hs
    show -1 < s.re; linarith [hs.1.1]
  have hh : DifferentiableOn ℂ (fun s => mellin φ s * (x : ℂ) ^ s) U := by
    intro s hs
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    exact ((hM s hs).mul
      (differentiableAt_id.const_cpow (Or.inl hx0))).differentiableWithinAt
  exact rectInt_logDeriv_mul hf hR hf2 (by simp; norm_num) (by simp; linarith) hrect hbd hUo hsubU hh



theorem explicit_formula_of_decay {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) {φ : ℝ → ℂ} {x : ℝ} (hx : 0 < x)
    (hM : ∀ s : ℂ, -1 < s.re → DifferentiableAt ℂ (mellin φ) s)
    (W : ℝ → ℝ) (hW : ∀ t : ℝ, 0 ≤ W t) (hanti : AntitoneOn W (Ici 0))
    (hstrip : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 3/2 → ‖mellin φ s‖ ≤ W |s.im|)
    (hdecay : Tendsto (fun k : ℕ => HkD B (k+1)*W ((k:ℝ)+1)) atTop (𝓝 0))
    (hright : Integrable fun y : ℝ => hIntD f φ x (((3/2:ℝ):ℂ)+y*I))
    (hleft : Integrable fun y : ℝ => hIntD f φ x (((-1/2:ℝ):ℂ)+y*I)) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) * (mellin φ u * (x : ℂ) ^ u))
        atTop (𝓝 ((1 / (2 * π) : ℂ) * ((∫ y : ℝ, hIntD f φ x (((3 / 2 : ℝ) : ℂ) + y * I)) -
          ∫ y : ℝ, hIntD f φ x (((-1 / 2 : ℝ) : ℂ) + y * I)))) := by
  choose T hT hgood using fun k : ℕ => good_heightD hd (k + 1)
  have hT' : ∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2) := fun k => by
    have := hT k; push_cast at this; constructor <;> linarith [this.1, this.2]
  refine ⟨T, hT', ?_⟩
  have hTpos : ∀ k, 0 < T k := fun k => by linarith [(hT' k).1, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  set Rinf := ∫ y : ℝ, hIntD f φ x (((3 / 2 : ℝ) : ℂ) + y * I) with hRinf
  set Linf := ∫ y : ℝ, hIntD f φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hLinf
  set Sk := fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) * (mellin φ u * (x : ℂ) ^ u)
  set Bot := fun k => ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), hIntD f φ x ((σ : ℂ) + ((-T k : ℝ) : ℂ) * I)
  set Top := fun k => ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), hIntD f φ x ((σ : ℂ) + ((T k : ℝ) : ℂ) * I)
  set Right := fun k => ∫ y in (-T k)..(T k), hIntD f φ x (((3 / 2 : ℝ) : ℂ) + y * I)
  set Left := fun k => ∫ y in (-T k)..(T k), hIntD f φ x (((-1 / 2 : ℝ) : ℂ) + y * I)
  -- the rectangle identity, expanded
  have hrect : ∀ k, Bot k - Top k + I * Right k - I * Left k = 2 * π * I * Sk k := by
    intro k
    have h := rect_identity_of_mellin_diff hd hM hx (hTpos k) (fun σ hσ => ((hgood k σ hσ).1).2)
      (fun σ hσ => ((hgood k σ hσ).1).1)
    rw [← h]
    unfold rectInt
    simp only [zT_re, zT_im, wT_re, wT_im, smul_eq_mul]
    rfl
  -- the horizontal sides
  have hside : ∀ k, ∀ S : ℝ, (S = T k ∨ S = -T k) →
      ‖∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), hIntD f φ x ((σ : ℂ) + (S : ℂ) * I)‖ ≤
        HkD B (k + 1) * W ((k:ℝ)+1) * (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ)) *
          |(3 / 2 : ℝ) - (-1 / 2)| := by
    intro k S hS
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
    have hσ' : σ ∈ [[(-1 / 2 : ℝ), 3 / 2]] := Set.uIoc_subset_uIcc hσ
    have hσ2 : -1 / 2 ≤ σ ∧ σ ≤ 3 / 2 := by
      rw [Set.uIcc_of_le (by norm_num)] at hσ'; exact hσ'
    have hb : ‖logDeriv f ((σ : ℂ) + (S : ℂ) * I)‖ ≤ HkD B (k + 1) := by
      rcases hS with rfl | rfl
      · exact ((hgood k σ hσ').2).1
      · exact ((hgood k σ hσ').2).2
    have hS' : |S| = T k := by
      rcases hS with rfl | rfl
      · exact abs_of_pos (hTpos k)
      · rw [abs_neg]; exact abs_of_pos (hTpos k)
    have hG := hstrip ((σ : ℂ) + (S : ℂ) * I) (by simp; linarith) (by simp; linarith)
    have him : ((σ : ℂ) + (S : ℂ) * I).im = S := by simp
    have hre : ((σ : ℂ) + (S : ℂ) * I).re = σ := by simp
    rw [him, hS'] at hG
    have hweight : W (T k) ≤ W ((k:ℝ)+1) :=
      hanti (mem_Ici.mpr (by positivity)) (mem_Ici.mpr (hTpos k).le) (hT' k).1
    have hWk0 : 0 ≤ W ((k:ℝ)+1) := hW _
    have hxσ := rpow_le_of_mem hx hσ2.1 hσ2.2
    have hHk0 : 0 ≤ HkD B (k + 1) := le_trans (norm_nonneg _) hb
    rw [hIntD, norm_mul, norm_mul, norm_cpow_x hx, hre]
    calc ‖logDeriv f ((σ : ℂ) + (S : ℂ) * I)‖ *
          (‖mellin φ ((σ : ℂ) + (S : ℂ) * I)‖ * x ^ σ)
        ≤ HkD B (k + 1) * (W ((k:ℝ)+1) *
          (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ))) := by
          gcongr
          exact hG.trans hweight
      _ = _ := by ring
  have hdecay : Tendsto (fun k : ℕ => HkD B (k + 1) * W ((k:ℝ)+1) *
      (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ)) * |(3 / 2 : ℝ) - (-1 / 2)|) atTop (𝓝 0) := by
    have h := (hdecay.mul_const (x ^ (3/2:ℝ)+x ^ (-1/2:ℝ))).mul_const
      |(3/2:ℝ)-(-1/2)|
    simpa only [zero_mul] using h
  have hBot : Tendsto Bot atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hside k (-T k) (Or.inr rfl)) hdecay
  have hTop : Tendsto Top atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hside k (T k) (Or.inl rfl)) hdecay
  have hTtop : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun k => (hT' k).1) (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hRight : Tendsto Right atTop (𝓝 Rinf) :=
    intervalIntegral_tendsto_integral (hright)
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  have hLeft : Tendsto Left atTop (𝓝 Linf) :=
    intervalIntegral_tendsto_integral (hleft)
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  have hSk : ∀ k, Sk k = (Bot k - Top k + I * Right k - I * Left k) / (2 * π * I) := by
    intro k
    have hne : (2 * π * I : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
    rw [hrect k]; field_simp
  have hlim := ((((hBot.sub hTop).add (hRight.const_mul I)).sub (hLeft.const_mul I)).div_const
    (2 * π * I))
  rw [show Sk = fun k => (Bot k - Top k + I * Right k - I * Left k) / (2 * π * I) from funext hSk]
  convert hlim using 2
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring


#print axioms rect_identity_of_mellin_diff
#print axioms explicit_formula_of_decay
end ChenEffective.PlattWindow.ContourDecay
