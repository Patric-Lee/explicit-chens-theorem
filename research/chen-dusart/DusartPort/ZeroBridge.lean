import DusartPort.ZeroMoment
import DusartPort.Lab.ExplicitPsi1.ZeroSum

/-! Connect the actual zeta zeros in the explicit formula to the xi divisor.
Both the locations and their multiplicities are proved here. -/
noncomputable section
namespace ChenEffective
open Complex Set Filter
open Complex.Hadamard
open scoped Topology
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem dusart_zeta_zero_endpoints {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    ρ ≠ 0 ∧ ρ ≠ 1 := by
  constructor
  · intro h
    norm_num [h, riemannZeta_zero] at hρ
  · intro h
    exact riemannZeta_ne_zero_of_one_le_re (s := 1) (by norm_num) (h ▸ hρ)

theorem dusart_zeta_zero_gamma_ne {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre : (-1 / 2 : ℝ) ≤ ρ.re) : Gammaℝ ρ ≠ 0 := by
  have h0 := (dusart_zeta_zero_endpoints hρ).1
  intro h
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp h
  have hr := congrArg Complex.re hn
  norm_num at hr
  have hnr : (n : ℝ) < 1 := by linarith only [hr, hre]
  have hn0 : n = 0 := by
    have hh : n < 1 := by exact_mod_cast hnr
    omega
  apply h0
  simpa [hn0] using hn

theorem dusart_zeta_zero_is_xi_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre : (-1 / 2 : ℝ) ≤ ρ.re) : riemannXi ρ = 0 := by
  obtain ⟨h0, h1⟩ := dusart_zeta_zero_endpoints hρ
  have hg := dusart_zeta_zero_gamma_ne hρ hre
  have hc : completedRiemannZeta ρ = riemannZeta ρ * Gammaℝ ρ :=
    ((eq_div_iff hg).mp (riemannZeta_def_of_ne_zero h0)).symm
  rw [riemannXi_eq_mul_completedRiemannZeta h0 h1, hc, hρ]
  simp

theorem dusart_zeta_zero_multiplicity {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre : (-1 / 2 : ℝ) ≤ ρ.re) :
    Int.toNat (MeromorphicOn.divisor riemannXi (Set.univ : Set ℂ) ρ) =
      analyticOrderNatAt riemannZeta ρ := by
  obtain ⟨h0, h1⟩ := dusart_zeta_zero_endpoints hρ
  have hg := dusart_zeta_zero_gamma_ne hρ hre
  let g : ℂ → ℂ := fun s => (2 / (s * (s - 1))) * (Gammaℝ s)⁻¹
  have ha : AnalyticAt ℂ g ρ := by
    apply AnalyticAt.mul
    · exact analyticAt_const.div (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
        (mul_ne_zero h0 (sub_ne_zero.mpr h1))
    · exact differentiable_Gammaℝ_inv.analyticAt ρ
  have hgne : g ρ ≠ 0 := by
    dsimp [g]
    exact mul_ne_zero
      (div_ne_zero (by norm_num) (mul_ne_zero h0 (sub_ne_zero.mpr h1))) (inv_ne_zero hg)
  have heq : riemannZeta =ᶠ[nhds ρ] fun s => g s * riemannXi s := by
    filter_upwards [eventually_ne_nhds h0, eventually_ne_nhds h1] with s hs0 hs1
    rw [riemannZeta_def_of_ne_zero hs0, riemannXi_eq_mul_completedRiemannZeta hs0 hs1]
    dsimp [g]
    field_simp
  have haxi := differentiable_riemannXi.analyticAt ρ
  have ho : analyticOrderAt riemannZeta ρ = analyticOrderAt riemannXi ρ := by
    rw [analyticOrderAt_congr heq]
    change analyticOrderAt (g * riemannXi) ρ = analyticOrderAt riemannXi ρ
    rw [analyticOrderAt_mul ha haxi,
      analyticOrderAt_eq_zero.mpr (Or.inr hgne), zero_add]
  have hnat : analyticOrderNatAt riemannZeta ρ = analyticOrderNatAt riemannXi ρ := by
    simp only [analyticOrderNatAt, ho]
  rw [hnat, MeromorphicOn.divisor_apply
    (fun z _ => (differentiable_riemannXi.analyticAt z).meromorphicAt) (mem_univ _),
    haxi.meromorphicOrderAt_eq]
  cases hh : analyticOrderAt riemannXi ρ with
  | top => simp [analyticOrderNatAt, hh]
  | coe n => simp [analyticOrderNatAt, hh]

#print axioms dusart_zeta_zero_is_xi_zero
#print axioms dusart_zeta_zero_multiplicity

theorem dusart_zeta_zero_finite_moment (s : Finset ℂ)
    (hs : ∀ ρ ∈ s, riemannZeta ρ = 0 ∧ (-1 / 2 : ℝ) ≤ ρ.re) :
    (∑ ρ ∈ s, DusartPort.Lab.ExplicitPsi1.hw ρ) ≤ (3 / 25 : ℝ) := by
  classical
  let I := Σ ρ : s, Fin (analyticOrderNatAt riemannZeta ρ)
  let f : I → DusartXiZero := fun p =>
    ⟨⟨p.1, ⟨p.2.val, by
      rw [dusart_zeta_zero_multiplicity (hs p.1 p.1.property).1 (hs p.1 p.1.property).2]
      exact p.2.isLt⟩⟩, (dusart_zeta_zero_endpoints (hs p.1 p.1.property).1).1⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hfirst : a.1 = b.1 := Subtype.ext (congrArg divisorZeroIndex₀_val hab)
    have hsecond : a.2.val = b.2.val := congrArg (fun p : DusartXiZero => p.1.2.val) hab
    cases a with
    | mk a i =>
      cases b with
      | mk b j =>
        dsimp at hfirst hsecond
        cases hfirst
        have hij : i = j := Fin.ext hsecond
        cases hij
        rfl
  let K : DusartXiZero → ℝ := fun p =>
    ‖1 / (divisorZeroIndex₀_val p * (divisorZeroIndex₀_val p + 1))‖
  have hle : (∑ i : I, K (f i)) ≤ (3 / 25 : ℝ) := by
    calc
      _ = ∑ p ∈ Finset.univ.image f, K p := by rw [Finset.sum_image]; exact fun a _ b _ h => hf h
      _ ≤ ∑' p : DusartXiZero, K p :=
        dusart_xi_zero_absolute_moment.1.sum_le_tsum _ (fun p _ => norm_nonneg _)
      _ ≤ _ := dusart_xi_zero_absolute_moment.2
  have hid : (∑ i : I, K (f i)) = ∑ ρ ∈ s, DusartPort.Lab.ExplicitPsi1.hw ρ := by
    rw [Fintype.sum_sigma]
    simp only [K, f, divisorZeroIndex₀_val, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.sum_attach s]
    apply Finset.sum_congr rfl
    intro ρ _
    unfold DusartPort.Lab.ExplicitPsi1.hw
    rw [norm_div, norm_one]
    ring
  rw [hid] at hle
  exact hle

#print axioms dusart_zeta_zero_finite_moment

theorem dusart_zeta_zero_absolute_moment :
    (∑' ρ : DusartPort.Lab.ExplicitPsi1.Zall,
      DusartPort.Lab.ExplicitPsi1.hw ρ) ≤ (3 / 25 : ℝ) := by
  classical
  apply Real.tsum_le_of_sum_le
    (fun ρ : DusartPort.Lab.ExplicitPsi1.Zall => DusartPort.Lab.ExplicitPsi1.hw_nonneg ρ)
  intro s
  have hmem : ∀ ρ ∈ s.image (fun z : DusartPort.Lab.ExplicitPsi1.Zall => z.val),
      riemannZeta ρ = 0 ∧ (-1 / 2 : ℝ) ≤ ρ.re := by
    intro ρ hρ
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hρ
    exact p.property
  have hh := dusart_zeta_zero_finite_moment
    (s.image (fun z : DusartPort.Lab.ExplicitPsi1.Zall => z.val)) hmem
  rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)] at hh
  exact hh

#print axioms dusart_zeta_zero_absolute_moment
end ChenEffective
