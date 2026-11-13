import OpenAIGrouped.Unit059
import OpenAIGrouped.Unit060
import OpenAIGrouped.Unit061
import OpenAIGrouped.Unit040

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondOriginalBound.lean; sha256: fe75c148cce8c5a693cbc10003e703d570feccc17c8fe915d666d936ee7ef226 -/
section Source2480
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_mode_original_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i∈J₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈J₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A)
    (hright : ∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A) :
    ‖∑ x∈source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤ A * ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  have hlabels' : ∀ x∈source,(actualSecondChild p u v x).2.1 ∈ labels := by
    intro x hx
    rw [actualSecondChild_label_units]
    exact hlabels x hx
  have hΓ := assigned_second_triples_subset p u v source J₁ J₂ lists₁ lists₂
  apply (actual_second_mode_branch_energy p hp hcop hg hpr hinj hc u v source hs pool Ψ hΨ m z
    slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels
    hlabels' hrows K ho hJ₁ hJ₂ w hw).trans
  apply (second_geometric_energy_of_bound K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
    _ _ _ A hA (fun γ hγ => hright γ (hΓ hγ)) (fun γ hγ => hleft γ (hΓ hγ))).trans
  exact mul_le_mul_of_nonneg_left (assigned_second_mass_le_original p u v source J₁ J₂ lists₁ lists₂ K) hA

end
end SevenEighths.InverseMoment

end OAI

end Source2480

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondAllModes.lean; sha256: d519c095def945927fca82d9ce467e2b2b7664fbd43c9a5e8ea7ce6c64fba8bd -/
section Source2481
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondAllModesUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondFullModeSum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
    ∑ x∈secondSourceSector source sector uv,
      actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
          ω₁ ω₂ G E V B X t

theorem secondFullModeSum_physical {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) :
    secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
      ω₁ ω₂ G E V B X w t =
    ∑ uv : Eisˣ × Eisˣ,∑ x∈secondSourceSector source sector uv,
      (w x*actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
        ∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
            ω₁ ω₂ G E V B X t := by
  unfold secondFullModeSum
  apply Finset.sum_congr rfl
  intro uv huv
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem actual_second_all_modes_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hslots₁ : slots₁.card ≤ K) (hslots₂ : slots₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A)
    (hright : ∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A) :
    ‖secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
      ω₁ ω₂ G E V B X w t‖ ≤
    36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  let mass := ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hbound (uv : Eisˣ × Eisˣ) (J₁ : Finset σ) (hJ₁ : J₁∈slots₁.powerset)
      (J₂ : Finset σ) (hJ₂ : J₂∈slots₂.powerset) :
      ‖∑ x∈secondSourceSector source sector uv,
        actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*w x*
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
            ω₁ ω₂ G E V B X t‖ ≤ A*mass := by
    have hsub : secondSourceSector source sector uv ⊆ source := Finset.filter_subset _ _
    have ht := actualSecondTriples_mono p 1 1 hsub
    have h := actual_second_mode_original_bound p hp hcop hg hpr hinj hc uv.1 uv.2
      (secondSourceSector source sector uv) (hs.mono p hsub) pool Ψ hΨ m z
      slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
      (fun i hi => ha₁ i (Finset.mem_powerset.mp hJ₁ hi))
      (fun i hi => ha₂ i (Finset.mem_powerset.mp hJ₂ hi)) ω₁ ω₂ G E V B X R t labels
      (fun x hx => hlabels x (hsub hx)) (fun x hx => hrows x (hsub hx)) K ho
      ((Finset.card_le_card (Finset.mem_powerset.mp hJ₁)).trans hslots₁)
      ((Finset.card_le_card (Finset.mem_powerset.mp hJ₂)).trans hslots₂)
      w (fun x hx => hw x (hsub hx)) A hA
      (fun γ hγ => hleft J₁ hJ₁ γ (ht hγ)) (fun γ hγ => hright J₂ hJ₂ γ (ht hγ))
    exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ht
      (fun γ _ _ => tripleDivisorWeight_nonneg K γ)) hA)
  calc
    _ ≤ ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
        ‖∑ x∈secondSourceSector source sector uv,
          actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*w x*
            secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
              ω₁ ω₂ G E V B X t‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro uv huv
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro J₁ hJ₁
      exact norm_sum_le _ _
    _ ≤ ∑ _uv : Eisˣ × Eisˣ,∑ _J₁∈slots₁.powerset,∑ _J₂∈slots₂.powerset,A*mass := by
      apply Finset.sum_le_sum
      intro uv huv
      apply Finset.sum_le_sum
      intro J₁ hJ₁
      exact Finset.sum_le_sum (fun J₂ hJ₂ => hbound uv J₁ hJ₁ J₂ hJ₂)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,
        second_unit_sector_card,Nat.cast_pow,Nat.cast_ofNat,mass]
      ring

end
end SevenEighths.InverseMoment

end OAI

end Source2481

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondAllIntegral.lean; sha256: 07662c3c7abefa239ee36ea62aee4359dbf00e7fe12b11f7e3896f0a97f63c52 -/
section Source2482
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondAllIntegralUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_all_modes_integral
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ)
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hslots₁ : slots₁.card ≤ K) (hslots₂ : slots₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A) (J : ℕ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ)
    (hDensity : Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
      tripleHeight J t.1*coordinateHeight J t.2*‖density t‖))
    (hleft : ∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A*(tripleHeight J t.1*coordinateHeight J t.2))
    (hright : ∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A*(tripleHeight J t.1*coordinateHeight J t.2)) :
    ‖∫ t : Frequency × (Fin 6 → ℝ),density t*secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
      ω₁ ω₂ G E V B X w t‖ ≤
    (36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
      ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖ := by
  let C := 36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
    ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hb (t : Frequency × (Fin 6 → ℝ)) :
      ‖secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X w t‖ ≤ C*(tripleHeight J t.1*coordinateHeight J t.2) := by
    have hh := actual_second_all_modes_bound p hp hcop hg hpr hinj hc source hs sector pool Ψ hΨ m z
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels hlabels hrows
      K ho hslots₁ hslots₂ w hw (A*(tripleHeight J t.1*coordinateHeight J t.2))
      (by unfold tripleHeight coordinateHeight; positivity) (hleft t) (hright t)
    exact hh.trans_eq (by dsimp only [C]; ring)
  calc
    _ ≤ ∫ t : Frequency × (Fin 6 → ℝ),C*(tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul C)
      filter_upwards with t
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

end
end SevenEighths.InverseMoment

end OAI

end Source2482

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondBalancedPhysical.lean; sha256: 2bf85c4ff98de91d70633555109323ba7cc122c65e671b5c6095fd5a2f694956 -/
section Source2483
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondBalancedPhysicalUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
universe u₁ u₂
variable {ι : Type u₁} {σ : Type u₂} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_balanced_profile_children
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B X Y R L : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ),
      0 < G → 0 < E → 0 < V → 0 < B → 0 < X → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*X^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₁ (primeProductNorm p N/X) = 1) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₂ (primeProductNorm p N/X) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/X) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B X i) = 1) →
      (Real.exp (-6*L):ℂ) * ((Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G*V*X))) =
      ((Y : ℂ)*secondRayCoefficient z*((E*V*X : ℝ):ℂ)⁻¹) *
        ∫ t : Frequency × (Fin 6 → ℝ),density t *
          ∑ uv : Eisˣ × Eisˣ,∑ x ∈ secondSourceSector source sector uv,
            (w x*actualSecondSignedWeight p hp hcop hg Ψ
              (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
            ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
              secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
                ω₁ ω₂ G E V B X t := by
  obtain ⟨sector,hsector⟩ := actual_second_modes_common_sectors p hp hcop hg hpr (σ:=σ) source hs
  refine ⟨sector,?_⟩
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
  have hn : ∀ x ∈ source,(secondInheritedProfile p x Ψ m z).divisor ≠ 0 ∧
      (secondInheritedProfile p x Ψ m z).frequency ≠ 0 := by
    intro x hx
    refine ⟨primeSubsetGenerator_ne_zero _ _,?_⟩
    have hh := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) R _).mp (hrows x hx)
    intro he
    change x.second.frequency = 0 at he
    simp only [he,mul_zero,map_zero,norm_zero,zero_pow (by omega : 2 ≠ 0),lt_self_iff_false] at hh
    exact hh.1
  have he := actual_second_balanced_source p hp hcop hg source pool
    (fun x : MarkedSecondSource ι Jo 0 => secondInheritedProfile p x Ψ m z)
    (fun x : MarkedSecondSource ι Jo 0 => w x*actualSecondSignedWeight p hp hcop hg Ψ
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ U G E V B X Y L
    hG hE hV hB hX density hDensity hsep hn hω₁ hω₂ hcut
  calc
    _ = ((Y:ℂ)*secondRayCoefficient z) * ((Real.exp (-6*L):ℂ)*
        ∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G*V*X)) := by ring
    _ = _ := by
      rw [he]
      rw [←mul_assoc]
      apply congrArg (fun a : ℂ => ((Y:ℂ)*secondRayCoefficient z*((E*V*X:ℝ):ℂ)⁻¹)*a)
      apply integral_congr_ae
      filter_upwards with t
      apply congrArg (fun a : ℂ => density t*a)
      exact hsector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t _

end
end SevenEighths.InverseMoment

end OAI

end Source2483

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondPhysicalEnergy.lean; sha256: 771f16ef5dfd1bbde0919b95dac766cd553354187ccc97785d28027ec657e9e4 -/
section Source2484
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondPhysicalEnergyUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_balanced_physical_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B X Y R L : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K J : ℕ) (A : ℝ),
      0 < G → 0 < E → 0 < V → 0 < B → 0 < X → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*X^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₁ (primeProductNorm p N/X) = 1) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₂ (primeProductNorm p N/X) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/X) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B X i) = 1) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G*V*X))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*X : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
  obtain ⟨sector,hsector⟩ := actual_second_balanced_profile_children p hp hcop hg hpr (σ:=σ) source hs
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w labels K J A hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have he := hsector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
  have hb := actual_second_all_modes_integral p hp hcop hg hpr hinj hc source hs sector pool Ψ hΨ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ ω₁ ω₂ G E V B X R labels hlabels hrows
    K ho hslots₁ hslots₂ w hw A hA J density hWeighted hleft hright
  have hi : (∫ t : Frequency × (Fin 6 → ℝ),density t *
      ∑ uv : Eisˣ × Eisˣ,∑ x∈secondSourceSector source sector uv,
        (w x*actualSecondSignedWeight p hp hcop hg Ψ
          (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
          ∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
            secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
              ω₁ ω₂ G E V B X t) =
      ∫ t : Frequency × (Fin 6 → ℝ),density t*secondFullModeSum p hp hcop hg source sector pool Ψ m z
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X w t := by
    apply integral_congr_ae
    filter_upwards with t
    rw [secondFullModeSum_physical]
  rw [hi] at he
  have hexp : Real.exp (6*L)*Real.exp (-6*L) = 1 := by
    rw [←Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hn := congrArg norm he
  conv_lhs at hn => rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  conv_rhs at hn => rw [norm_mul]
  have hn' := congrArg (fun a : ℝ => Real.exp (6*L)*a) hn
  rw [←mul_assoc,hexp,one_mul] at hn'
  rw [←mul_assoc] at hn'
  rw [hn']
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end
end SevenEighths.InverseMoment

end OAI

end Source2484

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondPhysicalRecursive.lean; sha256: 0b73dc82ed38c0facb324076610350de80b103f8f7c1cb18ee2ef48956117556 -/
section Source2485
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondPhysicalRecursiveUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_balanced_physical_recursive
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K J : ℕ) (A : ℝ),
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*(Z^N)^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₁ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₂ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/(Z^N)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/(Z^N)) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B (Z^N) i) = 1) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B Y R L Z N Vlabel εchild
    U density w labels K J A hZ hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have he (H : ℝ) : Z^(max 0 N+Vlabel)*(A*Z^(max 0 N+Vlabel+εchild)*H) =
      (A*Z^(2*(max 0 N+Vlabel)+εchild))*H := by
    calc
      _ = A*(Z^(max 0 N+Vlabel)*Z^(max 0 N+Vlabel+εchild))*H := by ring
      _ = _ := by rw [←Real.rpow_add hZ]; congr 2; ring_nf
  apply actual_second_balanced_physical_energy p hp hcop hg hpr hinj hc source hs
    pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B (Z^N) Y R L
    U density w labels K J (A*Z^(2*(max 0 N+Vlabel)+εchild))
    hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels
    ho hslots₁ hslots₂ (mul_nonneg hA (Real.rpow_pos_of_pos hZ _).le) hWeighted
  · intro t J₁ hJ₁ γ hγ
    rw [second_left_normalized_energy p hp hcop hg K (labels.filter Squarefree)
      (nonzeroChildFrequencyBall 1 R) γ pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ Z N Vlabel hZ t]
    rw [normalized_child_energy_radical_puncture p hp hcop hg pool (secondRayMinus Ψ z)
      (actualSecondInheritedPuncture m γ)]
    exact (mul_le_mul_of_nonneg_left (hleft t J₁ hJ₁ γ hγ) (Real.rpow_pos_of_pos hZ _).le).trans_eq (he _)
  · intro t J₂ hJ₂ γ hγ
    rw [second_right_normalized_energy p hp hcop hg K (labels.filter Squarefree)
      R γ pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ Z N Vlabel hZ t]
    rw [normalized_child_energy_radical_puncture p hp hcop hg pool (secondRayPlus Ψ z)
      (actualSecondInheritedPuncture m γ)]
    exact (mul_le_mul_of_nonneg_left (hright t J₂ hJ₂ γ hγ) (Real.rpow_pos_of_pos hZ _).le).trans_eq (he _)

end
end SevenEighths.InverseMoment

end OAI

end Source2485

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondSourceAttachment.lean; sha256: c0332d40eeb79577ed064fbd64a22e25c758b23bf6b8bbf86c6e2a5113d357ea -/
section Source2486
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

@[ext] structure SecondParentSource (ι : Type*) (Jo : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  quotient : Ideal Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal

def attachSecondExpansion {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) : MarkedSecondSource ι Jo 0 where
  cube := parent.cube
  firstCommon := parent.firstCommon
  firstDivisor := parent.firstDivisor
  second := x
  quotient := parent.quotient
  oldAssigned := parent.oldAssigned
  newAssigned := Fin.elim0

def secondParentOf {Jo : ℕ} (x : MarkedSecondSource ι Jo 0) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := x.oldAssigned

omit [DecidableEq ι] in
theorem attachSecondExpansion_injective {Jo : ℕ} (parent : SecondParentSource ι Jo) :
    Function.Injective (attachSecondExpansion parent) := by
  intro x y h
  exact congrArg MarkedSecondSource.second h

omit [DecidableEq ι] in
theorem attachSecondExpansion_recover {Jo : ℕ} (x : MarkedSecondSource ι Jo 0) :
    attachSecondExpansion (secondParentOf x) x.second = x := by
  apply MarkedSecondSource.ext <;> try rfl
  funext i
  exact Fin.elim0 i

def secondSourceParentEquiv {Jo : ℕ} :
    SecondParentSource ι Jo × SecondExpansionData ι ≃ MarkedSecondSource ι Jo 0 where
  toFun x := attachSecondExpansion x.1 x.2
  invFun x := (secondParentOf x,x.second)
  left_inv x := by cases x; rfl
  right_inv := attachSecondExpansion_recover

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondParentLabel {Jo : ℕ} (parent : SecondParentSource ι Jo) : Eis :=
  (∏ i∈parent.firstCommon,p i)*jLabel p parent.cube.support
    (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit

def secondParentDivisor {Jo : ℕ} (parent : SecondParentSource ι Jo) : Eis :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) parent.firstDivisor

def secondParentPuncture {Jo : ℕ} (m : Eis) (parent : SecondParentSource ι Jo) : Eis :=
  (m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*
    b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit*secondParentDivisor p parent

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_source_conditions {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (source : Finset (SecondExpansionData ι))
    (ha : parent.cube.Admissible) (hC : Disjoint parent.firstCommon parent.cube.support)
    (hD : parent.firstDivisor ⊆ parent.firstCommon∪parent.cube.support)
    (hE : ∀ x∈source,x.divisor ⊆ x.sourceCommon)
    (hold : ∀ i,(parent.oldAssigned i).val ∣
      sourceIdeal p parent.cube.support*sourceIdeal p parent.firstCommon*parent.quotient)
    (hq : parent.quotient ≠ 0) :
    ActualSecondSourceConditions p (source.image (attachSecondExpansion parent)) := by
  constructor
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact ha
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hC
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hD
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hE y hy
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hold
  · intro x hx i
    exact Fin.elim0 i
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hq

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_inherited_profile {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) :
    secondInheritedProfile p (attachSecondExpansion parent x) Ψ m z =
      expansionProfileData p Ψ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) z ∅ ∅ x := rfl

theorem attached_signed_weight {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) :
    actualSecondSignedWeight p hp hcop hg Ψ
      (m*ConcretePrimeRowBridge.idealGenerator (attachSecondExpansion parent x).quotient) z
      (attachSecondExpansion parent x) =
    secondSignedSourceWeight p hp hcop hg Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) z x := rfl

theorem secondExpansionSource_attached
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (source : Finset (SecondExpansionData ι)) (hE : ∀ x∈source,x.divisor ⊆ x.sourceCommon)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hp hcop hg pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) z source
      (fun U => primeMark slots₁ lists₁ a₁ U*W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ U*W₂ (primeProductNorm p U/X)) Φ Y =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x∈source.image (attachSecondExpansion parent),
        actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  have he := secondExpansionSource_signed_profile p hp hcop hg hinj hpr pool Ψ
    (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
    z source hE ∅ ∅ slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ X Y
  simp only [Finset.empty_union] at he
  rw [he]
  congr 1
  rw [Finset.sum_image (fun x hx y hy h => attachSecondExpansion_injective parent h)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [attached_inherited_profile,attached_signed_weight]

end
end SevenEighths.InverseMoment

end OAI

end Source2486

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondParentAssembly.lean; sha256: 633567a182e5a799883741214eaccf456b4942b20a70f8764ebd64513f8e794b -/
section Source2487
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] in
@[simp] theorem secondParentOf_attach {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) : secondParentOf (attachSecondExpansion parent x) = parent := rfl

def attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι)) :
    Finset (MarkedSecondSource ι Jo 0) :=
  parents.biUnion (fun parent => (source parent).image (attachSecondExpansion parent))

omit [DecidableEq ι] in
theorem mem_attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (x : MarkedSecondSource ι Jo 0) :
    x∈attachedSecondFamily parents source ↔
      secondParentOf x∈parents ∧ x.second∈source (secondParentOf x) := by
  simp only [attachedSecondFamily,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨parent,hp,y,hy,rfl⟩
    exact ⟨hp,hy⟩
  · rintro ⟨hp,hx⟩
    exact ⟨secondParentOf x,hp,x.second,hx,attachSecondExpansion_recover x⟩

omit [DecidableEq ι] in
theorem sum_attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    {A : Type*} [AddCommMonoid A] (H : MarkedSecondSource ι Jo 0 → A) :
    ∑ x∈attachedSecondFamily parents source,H x =
      ∑ parent∈parents,∑ x∈source parent,H (attachSecondExpansion parent x) := by
  unfold attachedSecondFamily
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro parent hp
    exact Finset.sum_image (fun x hx y hy he => attachSecondExpansion_injective parent he)
  · intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hy
    exact hab (congrArg secondParentOf he).symm

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_family_conditions {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (ha : ∀ parent∈parents,parent.cube.Admissible)
    (hC : ∀ parent∈parents,Disjoint parent.firstCommon parent.cube.support)
    (hD : ∀ parent∈parents,parent.firstDivisor ⊆ parent.firstCommon∪parent.cube.support)
    (hE : ∀ parent∈parents,∀ x∈source parent,x.divisor ⊆ x.sourceCommon)
    (hold : ∀ parent∈parents,∀ i,(parent.oldAssigned i).val ∣
      sourceIdeal p parent.cube.support*sourceIdeal p parent.firstCommon*parent.quotient)
    (hq : ∀ parent∈parents,parent.quotient ≠ 0) :
    ActualSecondSourceConditions p (attachedSecondFamily parents source) := by
  have h (x : MarkedSecondSource ι Jo 0) (hx : x∈attachedSecondFamily parents source) :=
    (mem_attachedSecondFamily parents source x).mp hx
  constructor
  · intro x hx; exact ha (secondParentOf x) (h x hx).1
  · intro x hx; exact hC (secondParentOf x) (h x hx).1
  · intro x hx; exact hD (secondParentOf x) (h x hx).1
  · intro x hx; exact hE (secondParentOf x) (h x hx).1 x.second (h x hx).2
  · intro x hx i; exact hold (secondParentOf x) (h x hx).1 i
  · intro x hx i; exact Fin.elim0 i
  · intro x hx; exact hq (secondParentOf x) (h x hx).1

theorem secondExpansionSource_whole_parent_family
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (hE : ∀ parent∈parents,∀ x∈source parent,x.divisor ⊆ x.sourceCommon)
    (w : SecondParentSource ι Jo → ℂ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    (∑ parent∈parents,w parent*secondExpansionSource p hp hcop hg pool Ψ
      (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
      z (source parent)
      (fun U => primeMark slots₁ lists₁ a₁ U*W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ U*W₂ (primeProductNorm p U/X)) Φ Y) =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x∈attachedSecondFamily parents source,
        (w (secondParentOf x)*actualSecondSignedWeight p hp hcop hg Ψ
          (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  rw [sum_attachedSecondFamily]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro parent hparent
  rw [secondExpansionSource_attached p hp hcop hg hinj hpr parent (source parent) (hE parent hparent)]
  rw [Finset.sum_image (fun x hx y hy he => attachSecondExpansion_injective parent he)]
  simp only [Finset.mul_sum,secondParentOf_attach]
  apply Finset.sum_congr rfl
  intro x hx
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2487

/- Original source: OAI/NumberTheory/DirichletL/Inversion/FirstPriorityParents.lean; sha256: 6cdd50384fd65ac1631f786ba933d3590c4106ac0aa556e8a22f765e563ee706 -/
section Source2488
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseFirstPriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic
local notation "O" => ActualEisensteinCubic.O

@[ext] structure Source (ι : Type*) (Jo : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  quotientSupport : Finset ι
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

def extractedSupport (negative : Bool) (x : Source ι Jo) : Finset ι :=
  ((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪x.quotientSupport

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def parent (x : Source ι Jo) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := sourceIdeal p x.quotientSupport
  oldAssigned := x.oldAssigned

theorem parent_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (parent p (Jo:=Jo)) := by
  intro x y h
  apply Source.ext
  · exact congrArg SecondParentSource.cube h
  · exact congrArg SecondParentSource.firstCommon h
  · exact congrArg SecondParentSource.firstDivisor h
  · exact sourceIdeal_injective p hinj (congrArg SecondParentSource.quotient h)
  · exact congrArg SecondParentSource.oldAssigned h

def appendParent {Jn : ℕ} (x : SecondParentSource ι Jo)
    (q : Fin Jn→SmoothMobiusCorrection.PrimeIdeal) : SecondParentSource ι (Jo+Jn) where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := Fin.addCases x.oldAssigned q

def forgetAppended {Jn : ℕ} (x : SecondParentSource ι (Jo+Jn)) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := fun i=>x.oldAssigned (Fin.castAdd Jn i)

omit [DecidableEq ι] in
@[simp] theorem forget_append {Jn : ℕ} (x : SecondParentSource ι Jo)
    (q : Fin Jn→SmoothMobiusCorrection.PrimeIdeal) : forgetAppended (appendParent x q)=x := by
  apply SecondParentSource.ext <;> try rfl
  funext i
  simp only [forgetAppended,appendParent,Fin.addCases_left]

omit [DecidableEq ι] in
theorem appendParent_injective {Jn : ℕ} :
    Function.Injective (fun q : SecondParentSource ι Jo × (Fin Jn→SmoothMobiusCorrection.PrimeIdeal)=>
      appendParent q.1 q.2) := by
  intro q r h
  apply Prod.ext
  · simpa only [forget_append] using congrArg forgetAppended h
  · funext i
    simpa only [appendParent,Fin.addCases_right] using
      congrArg (fun x : SecondParentSource ι (Jo+Jn)=>x.oldAssigned (Fin.natAdd Jo i)) h

def attach (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) : SecondParentSource ι (Jo+(J.card+J.card)) :=
  appendParent (parent p q.1) (fun i=>sourcePrime p (pairedSlotAssignment J J q.2 i))

omit [DecidableEq σ] in
theorem attach_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) (J : Finset σ) :
    Function.Injective (attach p (Jo:=Jo) J) := by
  intro q r h
  have he := @appendParent_injective ι Jo (J.card+J.card)
    (parent p q.1,fun i=>sourcePrime p (pairedSlotAssignment J J q.2 i))
    (parent p r.1,fun i=>sourcePrime p (pairedSlotAssignment J J r.2 i)) h
  apply Prod.ext
  · exact parent_injective p hinj (congrArg Prod.fst he)
  · apply pairedSlotAssignment_injective J J
    funext i
    exact hinj (congrArg (fun q : SecondParentSource ι Jo ×
      (Fin (J.card+J.card)→SmoothMobiusCorrection.PrimeIdeal)=>(q.2 i).val) he)

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem forget_attach (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    forgetAppended (attach p J q)=parent p q.1 := forget_append _ _

def assignmentSource (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) :
    Finset (Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :=
  (source ×ˢ ((J.pi lists)×ˢ(J.pi lists))).filter
    (fun q=>∀ i,pairedSlotAssignment J J q.2 i∈extractedSupport negative q.1)

def assignedParents (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) : Finset (SecondParentSource ι (Jo+(J.card+J.card))) :=
  (assignmentSource source negative J lists).image (attach p J)

theorem sum_assignmentSource {A : Type*} [AddCommMonoid A]
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (H : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))→A) :
    ∑ q∈assignmentSource source negative J lists,H q =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),H (x,q) := by
  rw [assignmentSource,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem sum_assignedParents (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {A : Type*} [AddCommMonoid A] (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (H : SecondParentSource ι (Jo+(J.card+J.card))→A) :
    ∑ y∈assignedParents p source negative J lists,H y =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),H (attach p J (x,q)) := by
  rw [assignedParents,Finset.sum_image (fun _ _ _ _ h=>attach_injective p hinj J h)]
  exact sum_assignmentSource source negative J lists _

def coefficient (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) :
    SecondParentSource ι (Jo+(J.card+J.card))→ℂ :=
  Function.extend (attach p J) (fun q=>w q.1*pairedSlotWeight J J a a q.2) (fun _=>0)

omit [DecidableEq σ] in
theorem coefficient_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    coefficient p J a w (attach p J q)=w q.1*pairedSlotWeight J J a a q.2 :=
  (attach_injective p hinj J).extend_apply _ _ _

theorem paired_parent_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(star (primeMark J lists a (extractedSupport negative x))*
      primeMark J lists a (extractedSupport negative x))*H (parent p x)) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  rw [sum_assignedParents p hinj]
  apply Finset.sum_congr rfl
  intro x hx
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul,coefficient_attach p hinj,forget_attach]

theorem paired_parent_sq_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (extractedSupport negative x)‖^2 : ℝ)*H (parent p x)) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  simpa only [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,starRingEnd_apply] using
    paired_parent_sum p hinj source negative J lists a w H

lemma mem_assignmentSource (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (q : (∀ i∈J,ι)×(∀ i∈J,ι)) :
    (x,q)∈assignmentSource source negative J lists ↔ x∈source ∧
      q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)) := by
  rw [←paired_assignment_filter]
  simp only [assignmentSource,Finset.mem_filter,Finset.mem_product]
  tauto

theorem mem_assignedParents (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    y∈assignedParents p source negative J lists ↔
      ∃ x∈source,∃ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),attach p J (x,q)=y := by
  simp only [assignedParents,Finset.mem_image]
  constructor
  · rintro ⟨⟨x,q⟩,hq,he⟩
    exact ⟨x,(mem_assignmentSource source negative J lists x q).mp hq |>.1,
      q,(mem_assignmentSource source negative J lists x q).mp hq |>.2,he⟩
  · rintro ⟨x,hx,q,hq,he⟩
    exact ⟨(x,q),(mem_assignmentSource source negative J lists x q).mpr ⟨hx,hq⟩,he⟩

structure SourceValid (x : Source ι Jo) : Prop where
  admissible : x.cube.Admissible
  common_disjoint : Disjoint x.firstCommon x.cube.support
  first_divisor : x.firstDivisor⊆x.firstCommon∪x.cube.support
  old_support : ∀ i,(x.oldAssigned i).val∣
    sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*sourceIdeal p x.quotientSupport

theorem extracted_prime_dvd (x : Source ι Jo) (hx : x.cube.Admissible)
    (negative : Bool) (i : ι) (hi : i∈extractedSupport negative x) :
    (sourcePrime p i).val∣sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*
      sourceIdeal p x.quotientSupport := by
  obtain hi|hi := Finset.mem_union.mp hi
  · obtain hi|hi := Finset.mem_union.mp hi
    · have hb : i∈x.cube.support := by
        cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hi
        · exact hx.1 hi
        · exact hx.2 hi
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (source_prime_dvd p _ i hb) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _) _
  · exact dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _

theorem attach_old_support (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (hx : SourceValid p x)
    (q : (∀ i∈J,ι)×(∀ i∈J,ι))
    (hq : q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
      (J.pi (fun i=>lists i∩extractedSupport negative x))) :
    ∀ i,((attach p J (x,q)).oldAssigned i).val∣
      sourceIdeal p (attach p J (x,q)).cube.support*
        sourceIdeal p (attach p J (x,q)).firstCommon*(attach p J (x,q)).quotient := by
  have hh : ∀ i,pairedSlotAssignment J J q i∈extractedSupport negative x := by
    have hf : q∈((J.pi lists)×ˢ(J.pi lists)).filter
        (fun q=>∀ i,pairedSlotAssignment J J q i∈extractedSupport negative x) := by
      rwa [paired_assignment_filter]
    exact (Finset.mem_filter.mp hf).2
  intro i
  refine Fin.addCases (fun k=>?_) (fun k=>?_) i
  · simpa only [attach,appendParent,parent,Fin.addCases_left] using hx.old_support k
  · simpa only [attach,appendParent,parent,Fin.addCases_right] using
      extracted_prime_dvd p x hx.admissible negative _ (hh k)

omit [DecidableEq σ] in

theorem attach_physical_data (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) (m : O) :
    secondParentLabel p (attach p J q)=secondParentLabel p (parent p q.1) ∧
    secondParentDivisor p (attach p J q)=secondParentDivisor p (parent p q.1) ∧
    secondParentPuncture p m (attach p J q)=secondParentPuncture p m (parent p q.1) :=
  ⟨rfl,rfl,rfl⟩

theorem coefficient_norm (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (B : ℝ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1) (hw : ∀ x∈source,‖w x‖≤B)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈assignedParents p source negative J lists) : ‖coefficient p J a w y‖≤B := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
  rw [coefficient_attach p hinj,norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pairedSlotWeight_norm_le_one J J lists lists a a
    _ q hq ha ha)).trans (hw x hx)

theorem assigned_family_conditions (hp : ∀ i,p i≠0)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (Jo+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀ y∈assignedParents p source negative J lists,∀ x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p (attachedSecondFamily (assignedParents p source negative J lists) expansion) := by
  apply attached_family_conditions p _ _
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).admissible
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).common_disjoint
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).first_divisor
  · exact hE
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact attach_old_support p negative J lists x (hs x hx) q hq
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact sourceIdeal_ne_zero p hp x.quotientSupport

def fixedPoint (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (D : Finset ι) : Source ι Jo :=
  ⟨b,C,E,D,old⟩

def fixedSource (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) : Finset (Source ι Jo) :=
  F.powerset.image (fixedPoint b C E old)

omit [DecidableEq ι] in
theorem fixedPoint_injective (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) : Function.Injective (fixedPoint b C E old) := by
  intro D D' h
  exact congrArg Source.quotientSupport h

def parentFunction (H : Source ι Jo→ℂ) : SecondParentSource ι Jo→ℂ :=
  Function.extend (parent p) H (fun _=>0)

theorem parentFunction_parent (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (H : Source ι Jo→ℂ) (x : Source ι Jo) : parentFunction p H (parent p x)=H x :=
  (parent_injective p hinj).extend_apply _ _ _

theorem paired_source_sq_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w H : Source ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (extractedSupport negative x)‖^2 : ℝ)*H x) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*parentFunction p H (forgetAppended y) := by
  simpa only [parentFunction_parent p hinj] using
    paired_parent_sq_sum p hinj source negative J lists a w (parentFunction p H)

theorem fixed_priority_complex (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w H : Finset ι→ℂ) :
    (∑ D∈F.powerset,w D*(‖primeMark J lists a
      (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2 : ℝ)*H D) =
    ∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>w x.quotientSupport) y *
        parentFunction p (fun x=>H x.quotientSupport) (forgetAppended y) := by
  have he := paired_source_sq_sum p hinj (fixedSource F b C E old) negative J lists a
    (fun x=>w x.quotientSupport) (fun x=>H x.quotientSupport)
  rw [fixedSource,Finset.sum_image (fun _ _ _ _ h=>fixedPoint_injective b C E old h)] at he
  simpa only [fixedPoint,extractedSupport,fixedSource] using he

theorem fixed_priority_slice (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : Finset ι→ℝ) :
    (∑ D∈F.powerset,w D*‖primeMark J lists a
      (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2) =
    (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>(w x.quotientSupport:ℂ)) y).re := by
  have he := paired_parent_sq_sum p hinj (fixedSource F b C E old) negative J lists a
    (fun x=>(w x.quotientSupport:ℂ)) (fun _=>1)
  simp only [mul_one] at he
  rw [fixedSource,Finset.sum_image (fun _ _ _ _ h=>fixedPoint_injective b C E old h)] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    fixedPoint,extractedSupport,fixedSource] using hr

variable (hp : ∀ i,p i≠0) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def priorityOuter (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter)
    (core : FirstCoreIndex) (D : Finset ι) : ℝ :=
  (‖RayFourExpansion.crossCoeff r.1 r.2‖*‖selector D‖) *
    ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit negative Ψ m D core‖

def priorityPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω : ℝ→ℂ) (X t Y : ℝ)
    (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter)
    (core : FirstCoreIndex) (D : Finset ι) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj F D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (fun U=>primeMark (slots\J)
      (fun i=>lists i\(((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)) a U)
    ω X (∏i∈C,p i) d core t Y

theorem first_priority_physical_slice (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ)
    (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter) (core : FirstCoreIndex) :
    (∑ D∈F.powerset,
      priorityOuter p hg b negative Ψ m selector r core D *
      ‖primeMark J lists a (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2 *
      (priorityPoisson p hp hg hinj F b C negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        slots J lists a ω X t Y r core D).re) =
    (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
      parentFunction p (fun x=>priorityPoisson p hp hg hinj F b C negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        slots J lists a ω X t Y r core x.quotientSupport) (forgetAppended y)).re := by
  have he := fixed_priority_complex p hinj F b C E old negative J lists a
    (fun D=>(priorityOuter p hg b negative Ψ m selector r core D:ℂ))
    (priorityPoisson p hp hg hinj F b C negative Ψ m
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) slots J lists a ω X t Y r core)
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero] using hr

theorem first_priority_energy_reindex (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) :
    firstPrioritySecondEnergy p hp hg hinj F b C negative Ψ m
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) slots lists a selector ω X t Y =
    (32*512)*(2:ℝ)^slots.card *
      ∑ r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter,
      ∑ core : FirstCoreIndex,∑ J∈slots.powerset,
      (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
        coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        parentFunction p (fun x=>priorityPoisson p hp hg hinj F b C negative Ψ m
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
          slots J lists a ω X t Y r core x.quotientSupport) (forgetAppended y)).re := by
  simp_rw [←first_priority_physical_slice p hp hg hinj]
  unfold firstPrioritySecondEnergy
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro core hcore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro D hD
  unfold priorityOuter priorityPoisson
  ring

end SevenEighths.InverseFirstPriorityParents

end

end OAI

end Source2488

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstWholeCubePriority.lean; sha256: eaa7b7d49ab530cccb2dca21bb85683fc3b12c42ecfdb6cc351d764cf67484f7 -/
section Source2489
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstWholePrioritySecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  let A := extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  (32*512)*(2:ℝ)^slots.card * ∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      ∑ J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2 *
        (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
          (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U)
          ω X (∏i∈C,p i) d core t Y).re

theorem first_actual_second_whole_cube_priority
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (F : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    firstCanonicalSecondEnergy p hp hg hinj F b C negative Ψ m d
      (fun U=>primeMark slots lists a (extra∪U)) selector ω X t Y ≤
    firstWholePrioritySecondEnergy p hp hg hinj F b C extra negative Ψ m d slots lists a selector ω X t Y := by
  let A := extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  have hb (r : RayCharacter×RayCharacter) (D : Finset ι) (core : FirstCoreIndex) :=
    first_fresh_priority_energy p hp hg hinj hc F D b.support A
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
      (if negative then r.1 else r.2) Ψ m slots lists a (fun _=>1)
      ω X (∏i∈C,p i) d core t Y hY
  simp only [mul_one] at hb
  unfold firstCanonicalSecondEnergy firstWholePrioritySecondEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro core hcore
  have h := mul_le_mul_of_nonneg_left (hb r D core)
    (show 0≤(32*512:ℝ)*(‖crossCoeff r.1 r.2‖*‖selector D‖)*
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖ from by positivity)
  convert h using 1
  · dsimp only [A]
    simp only [Finset.union_assoc]
    ring
  · simp only [A,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    ring

end
end SevenEighths.InverseMoment

end OAI

end Source2489

/- Original source: OAI/NumberTheory/DirichletL/Descent/WholePriorityParents.lean; sha256: bc4659a1512821ca2f99d2b7030ff7b9160d62f43f0be7dd3d95e323a6a2b436 -/
section Source2490
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentWholePriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

def wholeExtractedSupport (extra : Source ι Jo→Finset ι)
    (negative : Bool) (x : Source ι Jo) : Finset ι := extra x∪extractedSupport negative x

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def wholeAssignmentSource (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) :
    Finset (Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :=
  (source ×ˢ ((J.pi lists)×ˢ(J.pi lists))).filter
    (fun q=>∀ i,pairedSlotAssignment J J q.2 i∈wholeExtractedSupport extra negative q.1)

def wholeAssignedParents (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) : Finset (SecondParentSource ι (Jo+(J.card+J.card))) :=
  (wholeAssignmentSource extra source negative J lists).image (attach p J)

theorem sum_wholeAssignmentSource (extra : Source ι Jo→Finset ι) {A : Type*} [AddCommMonoid A]
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (H : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))→A) :
    ∑ q∈wholeAssignmentSource extra source negative J lists,H q =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),H (x,q) := by
  rw [wholeAssignmentSource,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem sum_wholeAssignedParents (extra : Source ι Jo→Finset ι) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {A : Type*} [AddCommMonoid A] (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (H : SecondParentSource ι (Jo+(J.card+J.card))→A) :
    ∑ y∈wholeAssignedParents p extra source negative J lists,H y =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),H (attach p J (x,q)) := by
  rw [wholeAssignedParents,Finset.sum_image (fun _ _ _ _ h=>attach_injective p hinj J h)]
  exact sum_wholeAssignmentSource extra source negative J lists _

theorem wholePaired_parent_sum (extra : Source ι Jo→Finset ι) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(star (primeMark J lists a (wholeExtractedSupport extra negative x))*
      primeMark J lists a (wholeExtractedSupport extra negative x))*H (parent p x)) =
    ∑ y∈wholeAssignedParents p extra source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  rw [sum_wholeAssignedParents p extra hinj]
  apply Finset.sum_congr rfl
  intro x hx
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul,coefficient_attach p hinj,forget_attach]

theorem wholePaired_parent_sq_sum (extra : Source ι Jo→Finset ι) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (wholeExtractedSupport extra negative x)‖^2 : ℝ)*H (parent p x)) =
    ∑ y∈wholeAssignedParents p extra source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  simpa only [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,starRingEnd_apply] using
    wholePaired_parent_sum p extra hinj source negative J lists a w H

lemma mem_wholeAssignmentSource (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (q : (∀ i∈J,ι)×(∀ i∈J,ι)) :
    (x,q)∈wholeAssignmentSource extra source negative J lists ↔ x∈source ∧
      q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)) := by
  rw [←paired_assignment_filter]
  simp only [wholeAssignmentSource,Finset.mem_filter,Finset.mem_product]
  tauto

theorem mem_wholeAssignedParents (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    y∈wholeAssignedParents p extra source negative J lists ↔
      ∃ x∈source,∃ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),attach p J (x,q)=y := by
  simp only [wholeAssignedParents,Finset.mem_image]
  constructor
  · rintro ⟨⟨x,q⟩,hq,he⟩
    exact ⟨x,(mem_wholeAssignmentSource extra source negative J lists x q).mp hq |>.1,
      q,(mem_wholeAssignmentSource extra source negative J lists x q).mp hq |>.2,he⟩
  · rintro ⟨x,hx,q,hq,he⟩
    exact ⟨(x,q),(mem_wholeAssignmentSource extra source negative J lists x q).mpr ⟨hx,hq⟩,he⟩

theorem whole_extracted_prime_dvd (extra : Source ι Jo→Finset ι)
    (x : Source ι Jo) (hx : x.cube.Admissible) (he : extra x⊆x.cube.support)
    (negative : Bool) (i : ι) (hi : i∈wholeExtractedSupport extra negative x) :
    (sourcePrime p i).val∣sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*
      sourceIdeal p x.quotientSupport := by
  obtain hi|hi := Finset.mem_union.mp hi
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (source_prime_dvd p _ i (he hi)) _) _
  · exact extracted_prime_dvd p x hx negative i hi

theorem whole_attach_old_support (extra : Source ι Jo→Finset ι)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (hx : SourceValid p x) (he : extra x⊆x.cube.support)
    (q : (∀ i∈J,ι)×(∀ i∈J,ι))
    (hq : q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
      (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))) :
    ∀ i,((attach p J (x,q)).oldAssigned i).val∣
      sourceIdeal p (attach p J (x,q)).cube.support*
        sourceIdeal p (attach p J (x,q)).firstCommon*(attach p J (x,q)).quotient := by
  have hh : ∀ i,pairedSlotAssignment J J q i∈wholeExtractedSupport extra negative x := by
    have hf : q∈((J.pi lists)×ˢ(J.pi lists)).filter
        (fun q=>∀ i,pairedSlotAssignment J J q i∈wholeExtractedSupport extra negative x) := by
      rwa [paired_assignment_filter]
    exact (Finset.mem_filter.mp hf).2
  intro i
  refine Fin.addCases (fun k=>?_) (fun k=>?_) i
  · simpa only [attach,appendParent,parent,Fin.addCases_left] using hx.old_support k
  · simpa only [attach,appendParent,parent,Fin.addCases_right] using
      whole_extracted_prime_dvd p extra x hx.admissible he negative _ (hh k)

theorem whole_assigned_family_conditions (hp : ∀ i,p i≠0)
    (extra : Source ι Jo→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (he : ∀ x∈source,extra x⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (Jo+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀ y∈wholeAssignedParents p extra source negative J lists,
      ∀ x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p
      (attachedSecondFamily (wholeAssignedParents p extra source negative J lists) expansion) := by
  apply attached_family_conditions p _ _
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).admissible
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).common_disjoint
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).first_divisor
  · exact hE
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact whole_attach_old_support p extra negative J lists x (hs x hx) (he x hx) q hq
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact sourceIdeal_ne_zero p hp x.quotientSupport

end SevenEighths.InverseMomentWholePriorityParents

end

end OAI

end Source2490

/- Original source: OAI/NumberTheory/DirichletL/Inversion/PrincipalEnergy.lean; sha256: eaf8f4171e5004025a871dfb81b6395faaa59ebbbe5deb7ae4f112c3a1818af2 -/
section Source2491
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InversePrincipalEnergy
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open SecondPassArithmetic FirstPassCubeLabels IdealMobiusDivisorSum
open InverseMoment
local notation "Eis" => ActualEisensteinCubic.O

section
variable {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem zero_norm_le (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1)
    (m c d : Eis) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 ≤ Y)
    (K : Finset ι → Finset ι → Finset Eis)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : Eis) ∈ K G E) :
    ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ ≤
      Y * ‖paperRadialFourier W 0‖ * ∑ G ∈ F.powerset, ‖H G‖ ^ 2 := by
  apply (truncatedSecondZero_norm_le p hg hinj F Ψ m c d H W Y K hzero).trans
  rw [abs_of_nonneg hY]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hY (norm_nonneg _))
  exact Finset.sum_le_sum (fun G _ => pow_le_pow_left₀ (norm_nonneg _)
    (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d H G) 2)

def supportIdeal (G : Finset ι) : Ideal Eis := ∏ i ∈ G, Ideal.span {p i}

omit [DecidableEq ι] in
lemma supportIdeal_ne_zero (G : Finset ι) : supportIdeal p G ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i}))

omit [DecidableEq ι] in
lemma supportIdeal_norm_pos (G : Finset ι) : 0 < (Ideal.absNorm (supportIdeal p G) : ℝ) := by
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (supportIdeal_ne_zero p G))

include hinj in

theorem mask_card_le_divisors (G : Finset ι) :
    G.powerset.card ≤ (idealDivisors (supportIdeal p G)).card := by
  apply Finset.card_le_card_of_injOn (supportIdeal p)
  · intro E hE
    apply (mem_idealDivisors (supportIdeal_ne_zero p G)).mpr
    exact Finset.prod_dvd_prod_of_subset E G (fun i => Ideal.span {p i}) (Finset.mem_powerset.mp hE)
  · intro E _ D _ h
    exact FirstCauchyArithmetic.family_product_injective (fun i => Ideal.span {p i}) hinj h

def principalFrequency (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ((Y : ℂ) / (‖eisEmbedding (∏ i ∈ (∅ : Finset ι) ∪ ∅, p i)‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p ((∅ : Finset ι) ∪ ∅))) *
    secondGaussTerm p hp hg hinj Ψ Ψ m r c d e k H₁ H₂ ∅ ∅

theorem principalFrequency_eq (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    principalFrequency p hg hinj hp Ψ m r c d e k H₁ H₂ W Y =
      (Y : ℂ) * paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 / ‖eisEmbedding e‖ ^ 2) *
        (star (H₁ ∅) * H₂ ∅) := by
  simp only [principalFrequency, Finset.union_empty, Finset.prod_empty, map_one, norm_one,
    Complex.ofReal_one, div_one, primeProductNorm, one_pow, mul_one,
    secondGaussTerm_empty (p := p) (hp := hp) (hg := hg) (hinj := hinj)]

theorem principalFrequency_eq_secondFrequencyKernel_empty
    (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    principalFrequency p hg hinj hp Ψ m r c d e k H₁ H₂ W Y =
      secondFrequencyKernel p hp hg hinj ∅ Ψ Ψ m r c d e k H₁ H₂ W Y := by
  simp only [secondFrequencyKernel, Finset.powerset_empty, Finset.sum_singleton,
    Finset.disjoint_empty_left, ite_true, principalFrequency]

def restorationTerm (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (G : Finset ι) (E : G.powerset) (k : Eis) : ℂ :=
  secondSourceCommonCoefficient p hg Ψ m c d G E.val *
    principalFrequency p hg hinj hp Ψ m
      (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

theorem restorationTerm_eq_principal_kernel (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ)
    (m c d : Eis) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (G : Finset ι) (E : G.powerset) (k : Eis) :
    restorationTerm p hg hinj hp Ψ m c d H W Y G E k =
      secondSourceCommonCoefficient p hg Ψ m c d G E.val *
        secondFrequencyKernel p hp hg hinj ∅ Ψ Ψ m
          (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
          (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y := by
  rw [restorationTerm, principalFrequency_eq_secondFrequencyKernel_empty]

theorem restorationTerm_eq (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (G : Finset ι) (E : G.powerset) (k : Eis) :
    restorationTerm p hg hinj hp Ψ m c d H W Y G E k =
      (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ) *
      (‖H G‖ ^ 2 : ℝ) * (UniqueFactorizationMonoid.moebius (supportIdeal p E.val) : ℂ) *
      ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ) : ℝ) : ℂ) *
      paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k‖ ^ 2) := by
  rw [restorationTerm, principalFrequency_eq]
  simp only [Finset.union_empty, secondSourceCommonCoefficient, primeSubsetGenerator_norm_sq]
  have hh : star (H G) * H G = (‖H G‖ ^ 2 : ℝ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hh]
  simp only [supportIdeal, Complex.ofReal_div]
  have harg : Y * ‖eisEmbedding k‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E.val, Ideal.span {p i}) : ℝ) =
      (Y / (Ideal.absNorm (∏ i ∈ E.val, Ideal.span {p i}) : ℝ)) * ‖eisEmbedding k‖ ^ 2 := by ring
  rw [harg]
  ring

theorem restorationTerm_mask_norm_le (hp : ∀ i, p i ≠ 0)
    (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (G : Finset ι) (E : G.powerset) (k : Eis) (θ : ℂ) (hθ : ‖θ‖ ≤ 1) :
    ‖θ * restorationTerm p hg hinj hp Ψ m c d H W Y G E k‖ ≤
      ‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        ‖paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k‖ ^ 2)‖ := by
  have ht := div_pos hY (supportIdeal_norm_pos p E.val)
  have ha : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      ((secondInputCoefficient_norm_le p hg Ψ m c d G).trans (hΨ _)) 2
  have hμ := QuadraticInitialBound.norm_ideal_moebius_le_one (supportIdeal p E.val)
  rw [restorationTerm_eq]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_norm, abs_of_pos ht]
  calc
    _ ≤ 1 * (1 * ‖H G‖ ^ 2 * 1 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        ‖paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k‖ ^ 2)‖) := by gcongr
    _ = _ := by ring

theorem restorationTerm_mask_summable_norm (hp : ∀ i, p i ≠ 0)
    (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (G : Finset ι) (E : G.powerset) (θ : Eis → ℂ)
    (hθ : ∀ k : {k : Eis // k ≠ 0}, ‖θ k.val‖ ≤ 1) :
    Summable (fun k : {k : Eis // k ≠ 0} =>
      ‖θ k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val‖) := by
  have ht := div_pos hY (supportIdeal_norm_pos p E.val)
  have hs := (paperRadialFourier_lattice_summable_norm W _ ht).subtype (fun k : Eis => k ≠ 0)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => restorationTerm_mask_norm_le p hg hinj hp Ψ hΨ m c d H W Y hY G E k.val (θ k.val) (hθ k))
    (hs.mul_left (‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ))))

theorem restoration_divisor_abs_le (hp : ∀ i, p i ≠ 0)
    (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (G : Finset ι) (E : G.powerset) (θ : Eis → ℂ)
    (hθ : ∀ k : {k : Eis // k ≠ 0}, ‖θ k.val‖ ≤ 1) :
    (∑' k : {k : Eis // k ≠ 0},
      ‖θ k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val‖) ≤
        QuadraticInitialBound.pvControl W * ‖H G‖ ^ 2 := by
  have ht := div_pos hY (supportIdeal_norm_pos p E.val)
  have hs := (paperRadialFourier_lattice_summable_norm W _ ht).subtype (fun k : Eis => k ≠ 0)
  have hb : (∑' k : {k : Eis // k ≠ 0},
      ‖θ k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val‖) ≤
      ∑' k : {k : Eis // k ≠ 0}, ‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        ‖paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k.val‖ ^ 2)‖ :=
    Summable.tsum_le_tsum
      (fun k : {k : Eis // k ≠ 0} => restorationTerm_mask_norm_le p hg hinj hp Ψ hΨ m c d H W Y hY G E k.val (θ k.val) (hθ k))
      (restorationTerm_mask_summable_norm p hg hinj hp Ψ hΨ m c d H W Y hY G E θ hθ)
      (hs.mul_left (‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ))))
  apply hb.trans
  calc
    _ = (‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ))) *
        (∑' k : {k : Eis // k ≠ 0}, ‖paperRadialFourier W
          ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k.val‖ ^ 2)‖) :=
      tsum_mul_left
    _ = ‖H G‖ ^ 2 * ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        (∑' k : {k : Eis // k ≠ 0}, ‖paperRadialFourier W
          ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k.val‖ ^ 2)‖)) := mul_assoc _ _ _
    _ ≤ ‖H G‖ ^ 2 * QuadraticInitialBound.pvControl W :=
      mul_le_mul_of_nonneg_left (QuadraticInitialBound.pv_lattice_bound W _ ht) (sq_nonneg ‖H G‖)
    _ = _ := mul_comm _ _

def principalRestoration (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (θ : Finset ι → Finset ι → Eis → ℂ) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset, ∑' k : {k : Eis // k ≠ 0},
    θ G E.val k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val

theorem principalRestoration_abs_le (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (θ : Finset ι → Finset ι → Eis → ℂ)
    (hθ : ∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) :
    (∑ G ∈ F.powerset, ∑ E : G.powerset, ∑' k : {k : Eis // k ≠ 0},
      ‖θ G E.val k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val‖) ≤
      QuadraticInitialBound.pvControl W *
        ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro G hG
  calc
    _ ≤ ∑ E : G.powerset, QuadraticInitialBound.pvControl W * ‖H G‖ ^ 2 :=
      Finset.sum_le_sum (fun E _ => restoration_divisor_abs_le p hg hinj hp Ψ hΨ m c d H W Y hY G E
        (θ G E.val) (hθ G hG E))
    _ = (G.powerset.card : ℝ) * (QuadraticInitialBound.pvControl W * ‖H G‖ ^ 2) := by simp
    _ ≤ ((idealDivisors (supportIdeal p G)).card : ℝ) *
        (QuadraticInitialBound.pvControl W * ‖H G‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast mask_card_le_divisors p hinj G)
        (mul_nonneg (QuadraticInitialBound.pvControl_nonneg W) (sq_nonneg _))
    _ = _ := by ring

theorem principalRestoration_norm_le (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (θ : Finset ι → Finset ι → Eis → ℂ)
    (hθ : ∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) :
    ‖principalRestoration p hg hinj hp F Ψ m c d H W Y θ‖ ≤
      QuadraticInitialBound.pvControl W *
        ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  apply (norm_sum_le _ _).trans
  apply le_trans _ (principalRestoration_abs_le p hg hinj hp F Ψ hΨ m c d H W Y hY θ hθ)
  apply Finset.sum_le_sum
  intro G hG
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro E _
  exact norm_tsum_le_tsum_norm (restorationTerm_mask_summable_norm p hg hinj hp Ψ hΨ m c d H W Y hY G E
    (θ G E.val) (hθ G hG E))

def markedRadial {σ : Type*} [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (V : 𝓢(ℝ, ℂ)) (X : ℝ) (G : Finset ι) : ℂ :=
  primeMark slots lists a (A ∪ G) * V (primeProductNorm p G / X)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma markedRadial_support {σ : Type*} [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (V : 𝓢(ℝ, ℂ)) (X M : ℝ) (hX : 0 < X)
    (hV : ∀ t, V t ≠ 0 → t ≤ Real.exp M) (G : Finset ι)
    (hG : markedRadial p slots lists a A V X G ≠ 0) :
    primeProductNorm p G ≤ X * Real.exp M := by
  have hv : V (primeProductNorm p G / X) ≠ 0 := by
    intro hz
    exact hG (by simp [markedRadial, hz])
  simpa only [mul_comm] using (div_le_iff₀ hX).mp (hV _ hv)

include hinj in

theorem radial_mass_from_pointwise (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (H : Finset ι → ℂ) (U ε D : ℝ)
    (hU : 0 < U) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hs : ∀ G, H G ≠ 0 → primeProductNorm p G ≤ U)
    (hb : ∀ G, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 ≤
      D * (primeProductNorm p G) ^ ε) :
    (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) ≤
      128 * D * U ^ (1 + ε) := by
  let T := boundedPrimeSupports p F U
  have he : (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) =
      ∑ G ∈ T, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro G hG hn
    have hz : H G = 0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hG, hs G hh⟩)
    simp [hz]
  rw [he]
  calc
    _ ≤ ∑ G ∈ T, D * U ^ ε := by
      apply Finset.sum_le_sum
      intro G hG
      exact (hb G).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (primeProductNorm_pos p hp G).le (Finset.mem_filter.mp hG).2 hε) hD)
    _ = (T.card : ℝ) * (D * U ^ ε) := by simp
    _ ≤ (128 * U) * (D * U ^ ε) := mul_le_mul_of_nonneg_right
      (boundedPrimeSupports_card_positive p hp hinj F U hU) (by positivity)
    _ = 128 * D * U ^ (1 + ε) := by rw [Real.rpow_add hU, Real.rpow_one]; ring

omit [DecidableEq ι] in
lemma mass_le_divisor_mass (F : Finset ι) (H : Finset ι → ℂ) :
    (∑ G ∈ F.powerset, ‖H G‖ ^ 2) ≤
      ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro G _
  have ho : (1 : Ideal Eis) ∈ idealDivisors (supportIdeal p G) :=
    (mem_idealDivisors (supportIdeal_ne_zero p G)).mpr (one_dvd _)
  have hc : (1 : ℝ) ≤ ((idealDivisors (supportIdeal p G)).card : ℝ) := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1, ho⟩
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (sq_nonneg ‖H G‖)

end

theorem marked_radial_divisor_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (V : 𝓢(ℝ, ℂ)) (X M : ℝ), 0 < X →
      (∀ t, V t ≠ 0 → t ≤ Real.exp M) →
      (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) *
        ‖markedRadial p slots lists a A V X G‖ ^ 2) ≤
        C * (4 : ℝ)^A.card * (SchwartzMap.seminorm ℝ 0 0 V)^2 *
          (X * Real.exp M)^(1 + ε) := by
  obtain ⟨Cm, hCm, hm⟩ := finite_primeMark_extracted_bound (ε / 4) (by positivity)
  obtain ⟨Cd, hCd, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨128 * Cd * Cm ^ 2, by positivity, ?_⟩
  intro ι σ _ _ p hp _ hinj hcop slots lists a hslots ha A F V X M hX hV
  have hpoint (G : Finset ι) :
      ((idealDivisors (supportIdeal p G)).card : ℝ) *
        ‖markedRadial p slots lists a A V X G‖ ^ 2 ≤
      (Cd * ((2 : ℝ)^A.card * Cm * SchwartzMap.seminorm ℝ 0 0 V)^2) *
        (primeProductNorm p G)^ε := by
    have hn := primeProductNorm_pos p hp G
    have hmark := hm p hp hcop slots lists a hslots ha A G
    have hv := V.norm_le_seminorm ℝ (primeProductNorm p G / X)
    have hdiv := hd (supportIdeal p G) (supportIdeal_ne_zero p G)
    rw [show (Ideal.absNorm (supportIdeal p G) : ℝ) = primeProductNorm p G from
      (primeProductNorm_eq_ideal_norm p G).symm] at hdiv
    have hpow : (primeProductNorm p G) ^ (ε / 2) * ((primeProductNorm p G) ^ (ε / 4))^2 =
        (primeProductNorm p G)^ε := by
      rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_add hn]
      congr 1
      ring
    calc
      _ ≤ (Cd * (primeProductNorm p G)^(ε/2)) *
          (((2 : ℝ)^A.card * Cm * (primeProductNorm p G)^(ε/4)) *
            SchwartzMap.seminorm ℝ 0 0 V)^2 := by
        apply mul_le_mul hdiv _ (sq_nonneg _) (by positivity)
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [markedRadial, norm_mul]
        exact mul_le_mul hmark hv (norm_nonneg _) (by positivity)
      _ = (Cd * ((2 : ℝ)^A.card * Cm * SchwartzMap.seminorm ℝ 0 0 V)^2) *
          ((primeProductNorm p G)^(ε/2) * ((primeProductNorm p G)^(ε/4))^2) := by ring
      _ = _ := by rw [hpow]
  have hb := radial_mass_from_pointwise p hinj hp F (markedRadial p slots lists a A V X)
    (X * Real.exp M) ε (Cd * ((2 : ℝ)^A.card * Cm * SchwartzMap.seminorm ℝ 0 0 V)^2)
    (by positivity) hε.le (by positivity)
    (markedRadial_support p slots lists a A V X M hX hV) hpoint
  have h4 : ((2 : ℝ)^A.card)^2 = (4 : ℝ)^A.card := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  convert hb using 1 ; (rw [mul_pow, mul_pow, h4]; ring)

lemma radial_support_of_annular (V : 𝓢(ℝ, ℂ)) (a M : ℝ)
    (hV : tsupport V ⊆ Set.Icc a (Real.exp M)) :
    ∀ t, V t ≠ 0 → t ≤ Real.exp M := by
  intro t ht
  exact (hV (subset_closure ht)).2

def outsideCutoff {ι : Type*} [DecidableEq ι]
    (K : Finset ι → Finset ι → Finset Eis) (G E : Finset ι) (k : Eis) : ℂ :=
  if k ∈ K G E then 0 else 1

lemma outsideCutoff_norm_le_one {ι : Type*} [DecidableEq ι]
    (K : Finset ι → Finset ι → Finset Eis) (G E : Finset ι) (k : Eis) :
    ‖outsideCutoff K G E k‖ ≤ 1 := by
  unfold outsideCutoff
  split_ifs <;> norm_num

lemma outsideCutoff_mul_norm_le_one {ι : Type*} [DecidableEq ι]
    (K : Finset ι → Finset ι → Finset Eis) (G E : Finset ι) (k : Eis)
    (θ : ℂ) (hθ : ‖θ‖ ≤ 1) : ‖outsideCutoff K G E k * θ‖ ≤ 1 := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul (outsideCutoff_norm_le_one K G E k) hθ
    (norm_nonneg _) zero_le_one

theorem uniform_row_control :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(ℝ, ℂ),
      ‖paperRadialFourier W 0‖ + QuadraticInitialBound.pvControl W ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 0
  refine ⟨s ∪ QuadraticInitialBound.pvSeminorms,
    C + QuadraticInitialBound.pvConstant, add_pos hC QuadraticInitialBound.pvConstant_pos, ?_⟩
  intro W
  have h₁ := Seminorm.le_def.mp (Finset.sup_mono (f := schwartzSeminormFamily ℝ ℝ ℂ)
    (Finset.subset_union_left (s₁ := s) (s₂ := QuadraticInitialBound.pvSeminorms))) W
  have h₂ := Seminorm.le_def.mp (Finset.sup_mono (f := schwartzSeminormFamily ℝ ℝ ℂ)
    (Finset.subset_union_right (s₁ := s) (s₂ := QuadraticInitialBound.pvSeminorms))) W
  have hz : ‖paperRadialFourier W 0‖ ≤ C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    simpa only [pow_zero, one_mul] using hb W 0 le_rfl
  calc
    _ ≤ C * (s ∪ QuadraticInitialBound.pvSeminorms).sup (schwartzSeminormFamily ℝ ℝ ℂ) W +
        QuadraticInitialBound.pvConstant *
          (s ∪ QuadraticInitialBound.pvSeminorms).sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
      add_le_add (hz.trans (mul_le_mul_of_nonneg_left h₁ hC.le))
        (mul_le_mul_of_nonneg_left h₂ QuadraticInitialBound.pvConstant_pos.le)
    _ = _ := by ring

section
variable {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem principal_energy_le (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 1 ≤ Y)
    (K : Finset ι → Finset ι → Finset Eis)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : Eis) ∈ K G E)
    (θ : Finset ι → Finset ι → Eis → ℂ)
    (hθ : ∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) :
    ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ +
        ‖principalRestoration p hg hinj hp F Ψ m c d H W Y θ‖ ≤
      Y * (‖paperRadialFourier W 0‖ + QuadraticInitialBound.pvControl W) *
        ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hd : 0 ≤ ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 :=
    Finset.sum_nonneg (fun G _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  calc
    _ ≤ Y * ‖paperRadialFourier W 0‖ * ∑ G ∈ F.powerset, ‖H G‖ ^ 2 +
        QuadraticInitialBound.pvControl W *
          ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 :=
      add_le_add (zero_norm_le p hg hinj F Ψ hΨ m c d H W Y hY0.le K hzero)
        (principalRestoration_norm_le p hg hinj hp F Ψ hΨ m c d H W Y hY0 θ hθ)
    _ ≤ Y * ‖paperRadialFourier W 0‖ *
          (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) +
        Y * QuadraticInitialBound.pvControl W *
          (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (mass_le_divisor_mass p F H) (mul_nonneg hY0.le (norm_nonneg _))
      · exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_left (QuadraticInitialBound.pvControl_nonneg W) hY) hd
    _ = _ := by ring

end

theorem marked_principal_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (Ψ : Eis →* ℂ), (∀ z, ‖Ψ z‖ ≤ 1) →
      ∀ (m c d : Eis) (V W : 𝓢(ℝ, ℂ)) (X M Y : ℝ), 0 < X → 1 ≤ Y →
      (∀ t, V t ≠ 0 → t ≤ Real.exp M) →
      ∀ K : Finset ι → Finset ι → Finset Eis,
      (∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : Eis) ∈ K G E) →
      ∀ θ : Finset ι → Finset ι → Eis → ℂ,
      (∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) →
      ‖truncatedSecondZero p hg F Ψ m c d (markedRadial p slots lists a A V X) W Y K‖ +
        ‖principalRestoration p hg hinj hp F Ψ m c d (markedRadial p slots lists a A V X) W Y θ‖ ≤
      C * (4 : ℝ)^A.card *
        (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 V)^2) *
        Y * (X * Real.exp M)^(1 + ε) := by
  obtain ⟨s, Cr, hCr, hr⟩ := uniform_row_control
  obtain ⟨Cm, hCm, hm⟩ := marked_radial_divisor_mass ε hε
  refine ⟨s, Cr * Cm, mul_pos hCr hCm, ?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists a hslots ha A F Ψ hΨ m c d V W X M Y hX hY hV K hzero θ hθ
  apply (principal_energy_le p hg hinj hp F Ψ hΨ m c d
    (markedRadial p slots lists a A V X) W Y hY K hzero θ hθ).trans
  have hb := hm p hp hinj hcop slots lists a hslots ha A F V X M hX hV
  calc
    _ ≤ Y * (Cr * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
        (Cm * (4 : ℝ)^A.card * (SchwartzMap.seminorm ℝ 0 0 V)^2 *
          (X * Real.exp M)^(1 + ε)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hr W) (le_trans zero_le_one hY)) hb
        (Finset.sum_nonneg (fun G _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
        (mul_nonneg (le_trans zero_le_one hY) (mul_nonneg hCr.le (apply_nonneg _ _)))
    _ = _ := by ring

end SevenEighths.InversePrincipalEnergy

end

end OAI

end Source2491

/- Original source: OAI/NumberTheory/DirichletL/Descent/PrincipalChild.lean; sha256: 5bab368a51c1e00ecaed735cff008b8c4f3f3389c117a189f6742d09636db7bf -/
section Source2492
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InversePrincipalEnergy
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma zero_mem_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (hR : 0 ≤ R) :
    (0 : Eis) ∈ childFrequencyBall a R := by
  apply (mem_childFrequencyBall a ha R 0).mpr
  simpa using hR

def secondPhysicalCutoff {ι : Type*} [DecidableEq ι] (p : ι → Eis)
    (d : Eis) (R : ℝ) (_G E : Finset ι) : Finset Eis :=
  childFrequencyBall (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E) R

def secondPhysicalMask {ι : Type*} [DecidableEq ι] (p : ι → Eis)
    (d : Eis) (R : ℝ) (_G E : Finset ι) (k : Eis) : ℂ :=
  if k ∈ nonzeroChildFrequencyBall
    (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E) R then 1 else 0

lemma secondPhysicalMask_norm_le_one {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (d : Eis) (R : ℝ) (G E : Finset ι) (k : Eis) :
    ‖secondPhysicalMask p d R G E k‖ ≤ 1 := by
  unfold secondPhysicalMask
  split_ifs <;> norm_num

lemma secondPhysicalMask_exact {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (d : Eis) (hd : d ≠ 0) (R : ℝ) (G E : Finset ι) (k : Eis) :
    secondPhysicalMask p d R G E k =
      if 0 < ‖ConcreteTraceCRT.eisEmbedding
          (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E * k)‖^2 ∧
        ‖ConcreteTraceCRT.eisEmbedding
          (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E * k)‖^2 ≤ R
      then 1 else 0 := by
  unfold secondPhysicalMask
  have he := mem_nonzeroChildFrequencyBall
    (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E)
    (mul_ne_zero hd (primeSubsetGenerator_ne_zero _ _)) R k
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact (h₂ (he.mp h₁)).elim
  · exact (h₁ (he.mpr h₂)).elim
  · rfl

theorem physical_child_principal_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (Ψ : Eis →* ℂ), (∀ z, ‖Ψ z‖ ≤ 1) →
      ∀ (m c d : Eis), d ≠ 0 → ∀ (V W : 𝓢(ℝ, ℂ)) (X M Y R : ℝ),
      0 < X → 1 ≤ Y → 0 ≤ R →
      (∀ t, V t ≠ 0 → t ≤ Real.exp M) →
      ‖truncatedSecondZero p hg F Ψ m c d (markedRadial p slots lists a A V X) W Y
        (secondPhysicalCutoff p d R)‖ +
      ‖principalRestoration p hg hinj hp F Ψ m c d (markedRadial p slots lists a A V X) W Y
        (secondPhysicalMask p d R)‖ ≤
      C * (4 : ℝ)^A.card *
        (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 V)^2) *
        Y * (X * Real.exp M)^(1 + ε) := by
  obtain ⟨s,C,hC,he⟩ := marked_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists a hs ha A F Ψ hΨ m c d hd V W X M Y R hX hY hR hV
  apply he p hp hg hinj hcop slots lists a hs ha A F Ψ hΨ m c d V W X M Y hX hY hV
  · intro G hG E hE
    exact zero_mem_childFrequencyBall _ (mul_ne_zero hd (primeSubsetGenerator_ne_zero _ _)) R hR
  · intro G hG E k
    exact secondPhysicalMask_norm_le_one p d R G E.val k.val

end
end SevenEighths.InverseMoment

end OAI

end Source2492

/- Original source: OAI/NumberTheory/DirichletL/Inversion/SecondPrincipalCaller.lean; sha256: d57b2ab59cecdc4dba9bc65ed3e6e71c0dddd7dd42109d8336c87133058ec232 -/
section Source2493
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseSecondPrincipalCaller
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge
open SecondPassIntegration CompletedHeight
open InverseMoment InversePrincipalEnergy RayFourExpansion
local notation "Eis" => ActualEisensteinCubic.O

def principalWindow (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  if negative then conjugateProfile (uniformTwistedSchwartz om a b ha hs (om.smooth ⊤) t)
  else uniformTwistedSchwartz om a b ha hs (om.smooth ⊤) t

theorem principalWindow_apply (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    principalWindow om a b ha hs negative t x =
      if negative then normTwistedSource (fun y => star (om y)) (-t) x
      else normTwistedSource om t x := by
  cases negative <;> simp only [principalWindow,Bool.false_eq_true,ite_false,ite_true,
    conjugateProfile_apply,uniformTwistedSchwartz_apply,normTwistedSource,
    star_mul,logPhase_conjugate,mul_comm]

theorem principalWindow_norm (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    ‖principalWindow om a b ha hs negative t x‖=‖om x‖ := by
  rw [principalWindow_apply]
  cases negative <;> simp [normTwistedSource,logPhase_norm]

theorem principalWindow_support (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) :
    Function.support (principalWindow om a b ha hs negative t) = Function.support om := by
  ext x
  change (_≠0) ↔ (_≠0)
  rw [←norm_ne_zero_iff,principalWindow_norm,norm_ne_zero_iff]

theorem principalWindow_seminorm_zero (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) :
    SchwartzMap.seminorm ℝ 0 0 (principalWindow om a b ha hs negative t)=
      SchwartzMap.seminorm ℝ 0 0 om := by
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
    intro x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero,principalWindow_norm]
      using SchwartzMap.norm_le_seminorm ℝ om x
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
    intro x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero,principalWindow_norm]
      using SchwartzMap.norm_le_seminorm ℝ (principalWindow om a b ha hs negative t) x

theorem principalWindow_upper (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (M : ℝ) (hb : b≤Real.exp M)
    (negative : Bool) (t x : ℝ) (hx : principalWindow om a b ha hs negative t x≠0) :
    x≤Real.exp M := by
  have hmem : x∈Function.support om := by
    rw [←principalWindow_support om a b ha hs negative t]
    exact hx
  exact (hs hmem).2.trans hb

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) (hp : ∀ i,p i≠0)

include hp in

theorem whole_columnLog (D U : Finset ι) (hDU : Disjoint D U) (X : ℝ) :
    columnLog p (primeProductNorm p D*X) (D∪U)=Real.log (primeProductNorm p U/X) := by
  unfold columnLog
  rw [primeProductNorm_union p D U hDU,
    mul_div_mul_left _ _ (primeProductNorm_pos p hp D).ne']

omit [DecidableEq σ] in

theorem primeMark_union_of_lists_disjoint (slots : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (D U : Finset ι)
    (hD : ∀ i∈slots,Disjoint (lists i) D) :
    primeMark slots lists coeff (D∪U)=primeMark slots lists coeff U := by
  unfold primeMark
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  have hh := Finset.disjoint_left.mp (hD i hi) hk
  simp only [Finset.mem_union,hh,false_or]

include hp in

theorem firstCoreTest_markedRadial (slots : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (D U : Finset ι) (hDU : Disjoint D U)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (negative : Bool) (X t : ℝ) (hX : 0<X) :
    firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D U =
    markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X U := by
  have ht : ∀ y : ℝ,logPhase (-t) (-y)=logPhase t y := by
    intro y
    unfold logPhase
    congr 1
    push_cast
    ring
  simp only [firstCoreTest,primeMark_union_of_lists_disjoint slots lists coeff D U hD,
    whole_columnLog p hp D U hDU X,ht,
    Real.exp_log (div_pos (primeProductNorm_pos p hp U) hX),
    markedRadial,Finset.empty_union,principalWindow]
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    conjugateProfile_apply,uniformTwistedSchwartz_apply,normTwistedSource,star_mul] <;> ring

variable [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem secondInputCoefficient_overlap_zero
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (D U : Finset ι)
    (hDU : ¬Disjoint D U) :
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d H U=0 := by
  rw [secondInputCoefficient_fixed_mask (p := p) (hg := hg),commonProduct_mask p hg hinj]
  split_ifs with h
  · exact (hDU h.symm).elim
  · exact zero_mul _

include hp in

theorem firstCoreTest_coefficient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ) (D U : Finset ι)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (negative : Bool) (X t : ℝ) (hX : 0<X) (Ψ : Eis→*ℂ) (m c d : Eis) :
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d
      (firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D) U =
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d
      (markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X) U := by
  by_cases hd : Disjoint D U
  · unfold secondInputCoefficient
    rw [firstCoreTest_markedRadial p hp slots lists coeff D U hd hD om a b ha hs negative X t hX]
  · rw [secondInputCoefficient_overlap_zero p hg hinj Ψ m c d _ D U hd,
      secondInputCoefficient_overlap_zero p hg hinj Ψ m c d _ D U hd]

omit [DecidableEq ι] in

theorem input_diagonal (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (U : Finset ι) :
    (‖secondInputCoefficient p hg Ψ m c d (fun _=>1) U‖^2 : ℝ) * star (H U) * H U =
      ((‖secondInputCoefficient p hg Ψ m c d H U‖^2 : ℝ) : ℂ) := by
  have he : secondInputCoefficient p hg Ψ m c d H U =
      secondInputCoefficient p hg Ψ m c d (fun _=>1) U * H U := by
    simp only [secondInputCoefficient,mul_one]
  have hh : star (H U)*H U=((‖H U‖^2 : ℝ):ℂ) := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  rw [he,norm_mul,mul_pow,Complex.ofReal_mul,mul_assoc,hh]

omit [DecidableEq ι] in
theorem input_norm_product (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (U : Finset ι) :
    (‖secondInputCoefficient p hg Ψ m c d (fun _=>1) U‖^2 : ℝ) * ‖H U‖^2 =
      ‖secondInputCoefficient p hg Ψ m c d H U‖^2 := by
  simp only [secondInputCoefficient,mul_one,norm_mul,mul_pow]

omit [DecidableEq ι] in

theorem zero_congr_input (F : Finset ι) (Ψ : Eis→*ℂ) (m c d : Eis)
    (H₁ H₂ : Finset ι→ℂ)
    (he : ∀ U,secondInputCoefficient p hg Ψ m c d H₁ U=
      secondInputCoefficient p hg Ψ m c d H₂ U)
    (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (K : Finset ι→Finset ι→Finset Eis) :
    truncatedSecondZero p hg F Ψ m c d H₁ W Y K=
      truncatedSecondZero p hg F Ψ m c d H₂ W Y K := by
  simp only [truncatedSecondZero,input_diagonal,he]

include hp in

theorem restoration_congr_input
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (Ψ : Eis→*ℂ) (m c d : Eis) (H₁ H₂ : Finset ι→ℂ)
    (he : ∀ U,secondInputCoefficient p hg Ψ m c d H₁ U=
      secondInputCoefficient p hg Ψ m c d H₂ U)
    (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (θ : Finset ι→Finset ι→Eis→ℂ) :
    principalRestoration p hg hinj hp F Ψ m c d H₁ W Y θ=
      principalRestoration p hg hinj hp F Ψ m c d H₂ W Y θ := by
  unfold principalRestoration
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro E hE
  apply tsum_congr
  intro k
  congr 1
  simp only [restorationTerm_eq,←Complex.ofReal_mul,input_norm_product,he]

include hp in

theorem firstCoreInputRow_principal_test
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t : ℝ) (hX : 0<X) (c d : Eis) (r : FirstCoreIndex) (z : Eis) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m (primeMark slots lists coeff)
      (fun u=>om (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) z =
    inputConjugateRow p hg F (firstCoreTwist negative χ Ψ r)
      ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i) (c*jLabel p B v ε₁ ε₂) d
      (markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X)
      (if negative then -z else z) := by
  rw [firstCoreInputRow_fixed_pool p hg hinj]
  unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
  apply Finset.sum_congr rfl
  intro U hU
  rw [firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX]

include hp in

theorem firstFreshSecondPoisson_markedRadial
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (c d : Eis) (r : FirstCoreIndex) :
    let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X
    let Ψ₀ := firstCoreTwist negative χ Ψ r
    let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
    let c₀ := c*jLabel p B v ε₁ ε₂
    firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
      (primeMark slots lists coeff) om X c d r t Y =
      ∑ G∈F.powerset,∑ U∈(F\G).powerset,∑ V∈(F\G).powerset,
        if Disjoint U V then overlapPairWeight p hg Ψ₀ m₀ c₀ d H₀ G U V *
          maskedSecondDual p hg hp hinj G U V rowMajorant Y else 0 := by
  intro H₀ Ψ₀ m₀ c₀
  let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
    (columnLog p (primeProductNorm p D*X)) negative (-t) D
  have he (z : Eis) : inputConjugateRow p hg F Ψ₀ m₀ c₀ d H z=
      inputConjugateRow p hg F Ψ₀ m₀ c₀ d H₀ z := by
    unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
    apply Finset.sum_congr rfl
    intro U hU
    rw [firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX]
  calc
    _ = ∑' z : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding z‖^2/Y)*
        (‖inputConjugateRow p hg F Ψ₀ m₀ c₀ d H z‖^2 : ℝ) := by
      rw [firstFreshSecondPoisson_fixed_pool p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m
        (primeMark slots lists coeff) om X c d r t Y hY]
      exact (inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ₀ m₀ c₀ d H
        rowMajorant Y hY).symm
    _ = ∑' z : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding z‖^2/Y)*
        (‖inputConjugateRow p hg F Ψ₀ m₀ c₀ d H₀ z‖^2 : ℝ) := by simp_rw [he]
    _ = _ := inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ₀ m₀ c₀ d H₀
      rowMajorant Y hY

theorem residual_lists_pairwise (slots J : Finset σ) (lists : σ→Finset ι) (A D : Finset ι)
    (h : (slots : Set σ).PairwiseDisjoint lists) :
    ((slots\J : Finset σ) : Set σ).PairwiseDisjoint (fun i=>lists i\(A∪D)) := by
  intro i hi j hj hij
  simp only [Finset.mem_coe,Finset.mem_sdiff] at hi hj
  exact (h hi.1 hj.1 hij).mono
    Finset.sdiff_subset Finset.sdiff_subset

omit [DecidableEq σ] in
theorem residual_lists_avoid (lists : σ→Finset ι) (A D : Finset ι) (i : σ) :
    Disjoint (lists i\(A∪D)) D := by
  apply Finset.disjoint_left.mpr
  intro k hk hkd
  exact (Finset.mem_sdiff.mp hk).2 (Finset.mem_union_right A hkd)

theorem residual_coeff_bound (slots J : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (A D : Finset ι)
    (h : ∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) :
    ∀ i∈slots\J,∀ k∈lists i\(A∪D),‖coeff i k‖≤1 := by
  intro i hi k hk
  exact h i (Finset.mem_sdiff.mp hi).1 k (Finset.mem_sdiff.mp hk).1

end Arithmetic

theorem firstCore_principal_energy (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      ∀ (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      (∀ i∈slots,Disjoint (lists i) D) →
      ∀ (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m c d : Eis),d≠0 → ∀ (r : FirstCoreIndex)
      (om W : 𝓢(ℝ,ℂ)) (a b : ℝ) (_ha : 0<a) (_hs : Function.support om⊆Set.Icc a b)
      (M t X Y R : ℝ),b≤Real.exp M → 0<X → 1≤Y → 0≤R →
      let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p B v ε₁ ε₂
      ‖truncatedSecondZero p hg F Ψ₀ m₀ c₀ d H W Y (secondPhysicalCutoff p d R)‖ +
      ‖principalRestoration p hg hinj hp F Ψ₀ m₀ c₀ d H W Y (secondPhysicalMask p d R)‖ ≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Y*(X*Real.exp M)^(1+ε) := by
  obtain ⟨s,C,hC,hbound⟩ := physical_child_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists coeff hslots hcoeff F D B v ε₁ ε₂ hD
    negative χ Ψ hΨ m c d hd r om W a b ha hs M t X Y R hb hX hY hR H Ψ₀ m₀ c₀
  let V := principalWindow om a b ha hs negative t
  let H₀ := markedRadial p slots lists coeff ∅ V X
  have he (U : Finset ι) : secondInputCoefficient p hg Ψ₀ m₀ c₀ d H U=
      secondInputCoefficient p hg Ψ₀ m₀ c₀ d H₀ U :=
    firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX Ψ₀
      (m*b0Label p B v ε₁ ε₂) c₀ d
  rw [zero_congr_input p hg F Ψ₀ m₀ c₀ d H H₀ he,
    restoration_congr_input p hp hg hinj F Ψ₀ m₀ c₀ d H H₀ he]
  have hbnd := hbound p hp hg hinj hcop slots lists coeff hslots hcoeff ∅ F Ψ₀
    (fun z=>(firstCoreTwist_norm_le negative χ Ψ r z).trans (hΨ z)) m₀ c₀ d hd V W X M Y R
    hX hY hR (principalWindow_upper om a b ha hs M hb negative t)
  simpa only [H₀,V,Finset.card_empty,pow_zero,mul_one,principalWindow_seminorm_zero] using hbnd

theorem priority_principal_energy (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots J : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      ∀ (F D B A : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m c d : Eis),d≠0 → ∀ (r : FirstCoreIndex)
      (om W : 𝓢(ℝ,ℂ)) (a b : ℝ) (_ha : 0<a) (_hs : Function.support om⊆Set.Icc a b)
      (M t X Y R : ℝ),b≤Real.exp M → 0<X → 1≤Y → 0≤R →
      let H := firstCoreTest (primeMark (slots\J) (fun i=>lists i\(A∪D)) coeff)
        (fun u=>om (Real.exp u)) (columnLog p (primeProductNorm p D*X)) negative (-t) D
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p B v ε₁ ε₂
      ‖truncatedSecondZero p hg F Ψ₀ m₀ c₀ d H W Y (secondPhysicalCutoff p d R)‖ +
      ‖principalRestoration p hg hinj hp F Ψ₀ m₀ c₀ d H W Y (secondPhysicalMask p d R)‖ ≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Y*(X*Real.exp M)^(1+ε) := by
  obtain ⟨s,C,hC,hbound⟩ := firstCore_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots J lists coeff hslots hcoeff F D B A v ε₁ ε₂
    negative χ Ψ hΨ m c d hd r om W a b ha hs M t X Y R hb hX hY hR
  exact hbound p hp hg hinj hcop (slots\J) (fun i=>lists i\(A∪D)) coeff
    (residual_lists_pairwise slots J lists A D hslots)
    (residual_coeff_bound slots J lists coeff A D hcoeff) F D B v ε₁ ε₂
    (fun i _=>residual_lists_avoid lists A D i) negative χ Ψ hΨ m c d hd r om W a b ha hs
    M t X Y R hb hX hY hR

end SevenEighths.InverseSecondPrincipalCaller

end

end OAI

end Source2493

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondParentInput.lean; sha256: 9baae7763ca3f8e5b865cfbbe1dd43bc4df720e206d501e18c2ca11a3bbae47e -/
section Source2494
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
theorem secondInputCoefficient_old_divisor_mask (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondInputCoefficient p hg Ψ (m*d) c d H S = secondInputCoefficient p hg Ψ m c d H S := by
  rw [secondInputCoefficient_fixed_mask p hg Ψ m d c d H S]
  have hd := row_power_mul_mask_power (fun i => Ideal.span {p i}) hg S d 1 1 (by decide)
  simp only [pow_one] at hd
  unfold secondInputCoefficient
  calc
    _ = Ψ (∏ i∈S,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) S m*
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c^4*
      (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d*
        rowCoprimeMask (fun i => Ideal.span {p i}) S d)*H S := by ring
    _ = _ := by rw [hd]

theorem inputConjugateRow_old_divisor_mask (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (k : Eis) :
    inputConjugateRow p hg F Ψ (m*d) c d H k = inputConjugateRow p hg F Ψ m c d H k := by
  simp only [inputConjugateRow,FirstCauchyArithmetic.supportConjugateSum,secondInputCoefficient_old_divisor_mask]

theorem inputConjugateRow_puncture_span (F : Finset ι) (Ψ : Eis →* ℂ) (m₁ m₂ c d : Eis)
    (hspan : Ideal.span {m₁} = (Ideal.span {m₂} : Ideal Eis)) (H : Finset ι → ℂ) (k : Eis) :
    inputConjugateRow p hg F Ψ m₁ c d H k = inputConjugateRow p hg F Ψ m₂ c d H k := by
  simp only [inputConjugateRow,FirstCauchyArithmetic.supportConjugateSum,secondInputCoefficient,
    rowCoprimeMask_eq_of_span_eq (fun i => Ideal.span {p i}) _ hspan]

theorem fresh_input_parent_mask {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (F D : Finset ι) (hq : parent.quotient = sourceIdeal p D)
    (Ψ : Eis →* ℂ) (m : Eis) (H : Finset ι → ℂ) (k : Eis) :
    inputConjugateRow p hg F Ψ
      ((m*b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
        parent.cube.leftBit parent.cube.rightBit)*∏ i∈D,p i)
      (secondParentLabel p parent) (secondParentDivisor p parent) H k =
    inputConjugateRow p hg F Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H k := by
  rw [←inputConjugateRow_old_divisor_mask]
  apply inputConjugateRow_puncture_span
  let b := b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit
  let d := secondParentDivisor p parent
  change Ideal.span {((m*b)*(∏ i∈D,p i))*d} =
    (Ideal.span {(m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*b*d} : Ideal Eis)
  rw [show ((m*b)*(∏ i∈D,p i))*d = (m*b*d)*(∏ i∈D,p i) by ring,
    show (m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*b*d =
      (m*b*d)*ConcretePrimeRowBridge.idealGenerator parent.quotient by ring]
  simp only [←Ideal.span_singleton_mul_span_singleton,
    ConcretePrimeRowBridge.span_idealGenerator,hq,sourceIdeal]

theorem first_fresh_parent_truncated
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (F D : Finset ι)
    (hq : parent.quotient = sourceIdeal p D)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X t Y : ℝ) (hY : 0 < Y) (core : FirstCoreIndex)
    (K : Finset ι → Finset ι → Finset Eis) :
    let Ψ₀ := firstCoreTwist negative χ Ψ core
    let H₀ := firstCoreTest H (fun u => ω (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D
    firstFreshSecondPoisson p hp hg hinj F D parent.cube.support
      (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit negative χ Ψ m H ω X
      (∏ i∈parent.firstCommon,p i) (secondParentDivisor p parent) core t Y =
    truncatedSecondSource p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
    secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K := by
  intro Ψ₀ H₀
  rw [firstFreshSecondPoisson_fixed_pool p hp hg hinj hc (hY:=hY)]
  rw [←inputConjugateRow_smoothed_second_poisson p hg hp hinj hc _ _ _ _ _ _ _ _ hY]
  change (∑' k : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding k‖^2/Y)*
    (‖inputConjugateRow p hg F Ψ₀
      ((m*b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
        parent.cube.leftBit parent.cube.rightBit)*∏ i∈D,p i)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ k‖^2 : ℝ)) = _
  simp_rw [fresh_input_parent_mask p hg parent F D hq Ψ₀ m H₀]
  exact inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc F Ψ₀ (secondParentPuncture p m parent)
    (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y hY K

end
end SevenEighths.InverseMoment

end OAI

end Source2494

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondFreshTruncation.lean; sha256: 0feecf6b90f60f837501cefa029a00cc79e04adbea066c59c97ca02a7251e76c -/
section Source2495
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_fresh_radial_truncated
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (c d : Eis) (r : FirstCoreIndex)
    (K : Finset ι → Finset ι → Finset Eis) :
    let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X
    let Ψ₀ := firstCoreTwist negative χ Ψ r
    let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
    let c₀ := c*jLabel p B v ε₁ ε₂
    firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
      (primeMark slots lists coeff) om X c d r t Y =
      truncatedSecondSource p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K +
        secondSourceTail p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K := by
  intro H₀ Ψ₀ m₀ c₀
  rw [firstFreshSecondPoisson_markedRadial p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    slots lists coeff hD om a b ha hs X t Y hX hY c d r]
  rw [←inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ₀ m₀ c₀ d H₀ rowMajorant Y hY]
  exact inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc F Ψ₀ m₀ c₀ d H₀ rowMajorant Y hY K

end
end SevenEighths.InverseMoment

end OAI

end Source2495

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondParentRadial.lean; sha256: abc60e4385e96c6d7c4e4e251ac2e67893cb342ec3d8f6e9c8c9382af8911a72 -/
section Source2496
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion
open InverseInitialArithmetic (sourceIdeal)
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_fresh_parent_radial_truncated
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (F D : Finset ι)
    (hq : parent.quotient = sourceIdeal p D)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (core : FirstCoreIndex)
    (K : Finset ι → Finset ι → Finset Eis) :
    let Ψ₀ := firstCoreTwist negative χ Ψ core
    let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X
    firstFreshSecondPoisson p hp hg hinj F D parent.cube.support
      (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit negative χ Ψ m (primeMark slots lists coeff) om X
      (∏ i∈parent.firstCommon,p i) (secondParentDivisor p parent) core t Y =
    truncatedSecondSource p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
    secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K := by
  intro Ψ₀ H₀
  let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
    (columnLog p (primeProductNorm p D*X)) negative (-t) D
  let m₀ := (m*b0Label p parent.cube.support
    (fun i=>parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit)*∏ i∈D,p i
  have he (k : Eis) : inputConjugateRow p hg F Ψ₀ m₀
      (secondParentLabel p parent) (secondParentDivisor p parent) H k =
    inputConjugateRow p hg F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ k := by
    calc
      _ = inputConjugateRow p hg F Ψ₀ m₀ (secondParentLabel p parent)
          (secondParentDivisor p parent) H₀ k := by
        unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
        apply Finset.sum_congr rfl
        intro U hU
        rw [firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX]
      _ = _ := fresh_input_parent_mask p hg parent F D hq Ψ₀ m H₀ k
  rw [firstFreshSecondPoisson_fixed_pool p hp hg hinj hc (hY:=hY)]
  rw [←inputConjugateRow_smoothed_second_poisson p hg hp hinj hc _ _ _ _ _ _ _ _ hY]
  change (∑' k : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding k‖^2/Y)*
    (‖inputConjugateRow p hg F Ψ₀ m₀ (secondParentLabel p parent)
      (secondParentDivisor p parent) H k‖^2 : ℝ)) = _
  simp_rw [he]
  exact inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc F Ψ₀ (secondParentPuncture p m parent)
    (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y hY K

end
end SevenEighths.InverseMoment

end OAI

end Source2496

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondVariableCutoff.lean; sha256: 560ec488ba5a5099764e2ea493fddec51154d0d1f9ba54c5e19dad0379259fb1 -/
section Source2497
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondVariableCutoff {Jo : ℕ} (parent : SecondParentSource ι Jo) (R : Finset ι → Finset ι → ℝ)
    (G E : Finset ι) : Finset Eis :=
  childFrequencyBall (secondParentDivisor p parent*primeSubsetGenerator (fun i => Ideal.span {p i}) E) (R G E)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_variable_original_support {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (pool residual : Finset ι) (R : Finset ι → Finset ι → ℝ)
    (label : Finset ι → SecondExpansionData ι → κ) (j : κ)
    (x : SecondExpansionData ι)
    (hx : x∈secondDyadicSector pool (secondVariableCutoff p parent R) residual label j) :
    x.sourceCommon ⊆ pool ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ pool ∧
    x.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p (attachSecondExpansion parent x)) (R x.sourceCommon x.divisor) := by
  obtain ⟨hx,hlabel⟩ := Finset.mem_filter.mp hx
  obtain ⟨hx,hresidual⟩ := Finset.mem_filter.mp hx
  exact (mem_secondExpansionPool _ _ _).mp hx

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_variable_attached_rows {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (pool residual : Finset ι) (R : Finset ι → Finset ι → ℝ)
    (label : Finset ι → SecondExpansionData ι → κ) (j : κ)
    (x : MarkedSecondSource ι Jo 0)
    (hx : x∈(secondDyadicSector pool (secondVariableCutoff p parent R) residual label j).image
      (attachSecondExpansion parent)) :
    x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R x.second.sourceCommon x.second.divisor) := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  exact (second_variable_original_support p parent pool residual R label j y hy).2.2.2

theorem truncated_second_attached_variable [Fintype κ]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι → Finset ι → ℝ)
    (label : Finset ι → SecondExpansionData ι → κ) :
    truncatedSecondSource p hp hg hinj pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent)
      (fun U => primeMark slots lists a U*W (primeProductNorm p U/X)) Φ Y
      (secondVariableCutoff p parent R) =
    truncatedSecondZero p hg pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent)
      (fun U => primeMark slots lists a U*W (primeProductNorm p U/X)) Φ Y
      (secondVariableCutoff p parent R) +
    ∑ z : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y : ℂ)*secondRayCoefficient z *
        ∑ x∈(secondDyadicSector pool (secondVariableCutoff p parent R) residual label j).image
          (attachSecondExpansion parent),
          actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x *
            actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
              slots slots lists lists a a W W Φ Y X := by
  rw [truncatedSecondSource_eq_zero_add_dyadic p hp hcop hg hinj hc hpr
    pool Ψ (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
    (fun U => primeMark slots lists a U*W (primeProductNorm p U/X)) Φ Y (secondVariableCutoff p parent R) label]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro residual hresidual
  apply Finset.sum_congr rfl
  intro j hj
  exact secondExpansionSource_attached p hp hcop hg hinj hpr parent _
    (fun x hx => (second_variable_original_support p parent pool residual R label j x hx).2.1)
    pool Ψ m z slots slots lists lists a a W W Φ X Y

end
end SevenEighths.InverseMoment

end OAI

end Source2497

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondCenterSector.lean; sha256: f329e6b15c1d9b0f60d0239168b6867ec4bc0b3a70ed5d4aa451315225b28810 -/
section Source2498
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι γ δ κ : Type*} [DecidableEq ι] [DecidableEq γ] [DecidableEq δ] [DecidableEq κ]

def secondCenterLabel (gIndex : Finset ι→γ) (thetaIndex : Finset ι→δ)
    (other : Finset ι→SecondExpansionData ι→κ) (residual : Finset ι)
    (x : SecondExpansionData ι) : γ × δ × κ :=
  (gIndex x.sourceCommon,thetaIndex x.divisor,other residual x)

theorem second_center_sector_rows (p : ι→Eis)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (pool residual : Finset ι)
    (gIndex : Finset ι→γ) (thetaIndex : Finset ι→δ)
    (other : Finset ι→SecondExpansionData ι→κ) (R : γ→δ→ℝ)
    (j : γ × δ × κ) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈(secondDyadicSector pool
      (secondVariableCutoff p parent (fun G E=>R (gIndex G) (thetaIndex E))) residual
      (secondCenterLabel gIndex thetaIndex other) j).image (attachSecondExpansion parent)) :
    x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R j.1 j.2.1) := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have hlabel := (Finset.mem_filter.mp hy).2
  have hg : gIndex y.sourceCommon=j.1 := congrArg Prod.fst hlabel
  have ht : thetaIndex y.divisor=j.2.1 := congrArg (fun a : γ×δ×κ=>a.2.1) hlabel
  obtain ⟨hy,_⟩ := Finset.mem_filter.mp hy
  obtain ⟨hy,_⟩ := Finset.mem_filter.mp hy
  have hs := ((mem_secondExpansionPool _ _ _).mp hy).2.2.2
  change y.frequency ∈ nonzeroChildFrequencyBall
    (actualSecondMultiplier p (attachSecondExpansion parent y)) (R (gIndex y.sourceCommon) (thetaIndex y.divisor)) at hs
  change y.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p (attachSecondExpansion parent y)) (R j.1 j.2.1)
  simpa only [hg,ht] using hs

theorem second_center_sector_empty (p : ι→Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (pool residual : Finset ι)
    (gIndex : Finset ι→γ) (thetaIndex : Finset ι→δ)
    (other : Finset ι→SecondExpansionData ι→κ) (R : γ→δ→ℝ)
    (j : γ × δ × κ) (hR : R j.1 j.2.1<1) :
    secondDyadicSector pool
      (secondVariableCutoff p parent (fun G E=>R (gIndex G) (thetaIndex E))) residual
      (secondCenterLabel gIndex thetaIndex other) j = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hs := second_center_sector_rows p parent pool residual gIndex thetaIndex other R j
    (attachSecondExpansion parent y) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
  have ha : actualSecondMultiplier p (attachSecondExpansion parent y) ≠ 0 :=
    mul_ne_zero (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _)
  rw [nonzeroChildFrequencyBall_empty _ ha _ hR] at hs
  exact Finset.notMem_empty _ hs

theorem second_center_sector_nonnegative (p : ι→Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (pool residual : Finset ι)
    (gIndex : Finset ι→γ) (thetaIndex : Finset ι→δ)
    (other : Finset ι→SecondExpansionData ι→κ) (M : γ→δ→ℝ) (Z : ℝ) (hZ : 1<Z)
    (j : γ × δ × κ)
    (hne : (secondDyadicSector pool
      (secondVariableCutoff p parent (fun G E=>Z^(M (gIndex G) (thetaIndex E)))) residual
      (secondCenterLabel gIndex thetaIndex other) j).Nonempty) : 0≤M j.1 j.2.1 := by
  by_contra hn
  have hlt : Z^(M j.1 j.2.1)<1 := Real.rpow_lt_one_of_one_lt_of_neg hZ (lt_of_not_ge hn)
  rw [second_center_sector_empty p parent pool residual gIndex thetaIndex other
    (fun a b=>Z^(M a b)) j hlt] at hne
  exact Finset.not_nonempty_empty hne

end
end SevenEighths.InverseMoment

end OAI

end Source2498

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondFullSource.lean; sha256: 8ffa1cc1ec1a5c7cf31f6f3ffe080a113d700c29290b6c0e9c1dd9f720019821 -/
section Source2499
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion
open InverseInitialArithmetic (sourceIdeal)
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ] [Fintype κ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_parent_full_second_source
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (F D : Finset ι)
    (hq : parent.quotient = sourceIdeal p D)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X height Y : ℝ) (hX : 0<X) (hY : 0<Y) (core : FirstCoreIndex)
    (R : Finset ι → Finset ι → ℝ) (label : Finset ι → SecondExpansionData ι → κ) :
    let Ψ₀ := firstCoreTwist negative χ Ψ core
    let V := principalWindow om a b ha hs negative height
    let H₀ := markedRadial p slots lists coeff ∅ V X
    let K := secondVariableCutoff p parent R
    firstFreshSecondPoisson p hp hg hinj F D parent.cube.support
      (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit negative χ Ψ m (primeMark slots lists coeff) om X
      (∏ i∈parent.firstCommon,p i) (secondParentDivisor p parent) core height Y =
    truncatedSecondZero p hg F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
    (∑ ray : SecondRayIndex,∑ residual∈F.powerset,∑ j : κ,
      (Y : ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector F K residual label j).image (attachSecondExpansion parent),
          actualSecondSignedWeight p hp hcop hg Ψ₀ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
            actualSecondProfileRow p hp hcop hg F (secondInheritedProfile p x Ψ₀ m ray)
              slots slots lists lists coeff coeff V V rowMajorant Y X) +
    secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K := by
  intro Ψ₀ V H₀ K
  have htest : H₀=(fun U=>primeMark slots lists coeff U*V (primeProductNorm p U/X)) := by
    funext U
    simp only [H₀,markedRadial,Finset.empty_union]
  have hret := truncated_second_attached_variable p hp hcop hg hinj hc hpr parent F Ψ₀ m
    slots lists coeff V rowMajorant X Y R label
  rw [←htest] at hret
  calc
    _ = truncatedSecondSource p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
        secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
          (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K :=
      first_fresh_parent_radial_truncated p hp hg hinj hc parent F D hq negative χ Ψ m
        slots lists coeff hD om a b ha hs X height Y hX hY core K
    _ = _ := congrArg (fun v=>v + secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K) hret

end
end SevenEighths.InverseMoment

end OAI

end Source2499

/- Original source: OAI/NumberTheory/DirichletL/Inversion/PrioritySecondSource.lean; sha256: 24fc0cb403c53b2d7567f31fb60b7658d2de89e0e6281a5c82311e84dc1a17dd -/
section Source2500
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InversePrioritySecondSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def quotientSupport (y : SecondParentSource ι Jo) : Finset ι :=
  Function.extend (sourceIdeal p) id (fun _=>∅) y.quotient

theorem quotientSupport_parent (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (x : Source ι Jo) : quotientSupport p (parent p x)=x.quotientSupport :=
  (sourceIdeal_injective p hinj).extend_apply _ _ _

omit [DecidableEq σ] in
theorem quotientSupport_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    quotientSupport p (attach p J q)=q.1.quotientSupport :=
  quotientSupport_parent p hinj q.1

def residualLists (negative : Bool) (lists : σ→Finset ι)
    (y : SecondParentSource ι Jo) (i : σ) : Finset ι :=
  lists i \ (((if negative then y.cube.rightDivisor else y.cube.leftDivisor)∪y.firstCommon)∪
    quotientSupport p y)

omit [DecidableEq σ] in
theorem residualLists_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    residualLists p negative lists (attach p J q)=
      fun i=>lists i\extractedSupport negative q.1 := by
  funext i
  unfold residualLists
  rw [quotientSupport_attach p hinj]
  rfl

omit [DecidableEq σ] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem residualLists_disjoint (negative : Bool) (lists : σ→Finset ι)
    (y : SecondParentSource ι Jo) (i : σ) :
    Disjoint (residualLists p negative lists y i) (quotientSupport p y) := by
  apply Finset.disjoint_left.mpr
  intro q hq hd
  exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_union_right _ hd)

theorem assigned_quotient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈assignedParents p source negative J lists) :
    y.quotient=sourceIdeal p (quotientSupport p y) := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
  rw [quotientSupport_attach p hinj]
  rfl

def retainedPool (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) : Finset (MarkedSecondSource ι Jo 0) :=
  attachedSecondFamily parents (fun y=>secondDyadicSector pool (secondVariableCutoff p y (R y))
    residual (label y) j)

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem mem_retainedPool (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι Jo 0) :
    x∈retainedPool p pool parents R label residual j ↔
      secondParentOf x∈parents ∧ x.second∈secondDyadicSector pool
        (secondVariableCutoff p (secondParentOf x) (R (secondParentOf x))) residual
        (label (secondParentOf x)) j := mem_attachedSecondFamily _ _ _

theorem retainedPool_conditions (hp : ∀ i,p i≠0)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p
      (retainedPool p pool (assignedParents p source negative J lists) R label residual j) := by
  apply assigned_family_conditions p hp source hs negative J lists
  intro y hy x hx
  exact (second_variable_original_support p y pool residual (R y) (label y) j x hx).2.1

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem retainedPool_original_support
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈retainedPool p pool parents R label residual j) :
    x.second.sourceCommon⊆pool ∧ x.second.divisor⊆x.second.sourceCommon ∧
    x.second.overlap⊆pool ∧ x.second.frequency∈nonzeroChildFrequencyBall
      (actualSecondMultiplier p x) (R (secondParentOf x) x.second.sourceCommon x.second.divisor) := by
  have hh := (mem_retainedPool p pool parents R label residual j x).mp hx
  simpa only [attachSecondExpansion_recover] using
    second_variable_original_support p (secondParentOf x) pool residual (R (secondParentOf x))
      (label (secondParentOf x)) j x.second hh.2

def attachOriginal (J : Finset σ)
    (q : (Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) × SecondExpansionData ι) :
    MarkedSecondSource ι (Jo+(J.card+J.card)) 0 :=
  attachSecondExpansion (attach p J q.1) q.2

omit [DecidableEq σ] in
theorem attachOriginal_injective (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) : Function.Injective (attachOriginal p (Jo:=Jo) J) := by
  intro q r he
  apply Prod.ext
  · apply attach_injective p hinj J
    exact congrArg secondParentOf he
  · exact congrArg MarkedSecondSource.second he

theorem retainedPool_iff_original
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0) :
    x∈retainedPool p pool (assignedParents p source negative J lists) R label residual j ↔
      ∃ s∈source,∃ q∈(J.pi (fun i=>lists i∩extractedSupport negative s))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative s)),
        ∃ e∈secondDyadicSector pool (secondVariableCutoff p (attach p J (s,q)) (R (attach p J (s,q))))
          residual (label (attach p J (s,q))) j,attachOriginal p J ((s,q),e)=x := by
  constructor
  · intro hx
    obtain ⟨hy,he⟩ := (mem_retainedPool p _ _ _ _ _ _ x).mp hx
    obtain ⟨s,hs,q,hq,ha⟩ := (mem_assignedParents p source negative J lists (secondParentOf x)).mp hy
    refine ⟨s,hs,q,hq,x.second,?_,?_⟩
    · simpa only [ha] using he
    · unfold attachOriginal
      rw [ha,attachSecondExpansion_recover]
  · rintro ⟨s,hs,q,hq,e,he,rfl⟩
    apply (mem_retainedPool p _ _ _ _ _ _ _).mpr
    refine ⟨?_,he⟩
    exact (mem_assignedParents p source negative J lists _).mpr ⟨s,hs,q,hq,rfl⟩

omit [DecidableEq σ] in
theorem attached_coefficient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) (e : SecondExpansionData ι) :
    coefficient p J a w (secondParentOf (attachOriginal p J (q,e)))=
      w q.1*pairedSlotWeight J J a a q.2 := coefficient_attach p hinj J a w q

variable (hp : ∀ i,p i≠0)
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varying_lists_parent_family
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo→Finset (SecondExpansionData ι))
    (hE : ∀ y∈parents,∀ x∈source y,x.divisor⊆x.sourceCommon)
    (w : SecondParentSource ι Jo→ℂ) (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : SecondParentSource ι Jo→σ→Finset ι)
    (a₁ a₂ : σ→ι→ℂ) (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    (∑ y∈parents,w y*secondExpansionSource p hp hcop hg pool Ψ
      (secondParentPuncture p m y) (secondParentLabel p y) (secondParentDivisor p y) z (source y)
      (fun U=>primeMark slots₁ (lists₁ y) a₁ U*W₁ (primeProductNorm p U/X))
      (fun U=>primeMark slots₂ (lists₂ y) a₂ U*W₂ (primeProductNorm p U/X)) Φ Y) =
    (Y:ℂ)*secondRayCoefficient z * ∑ x∈attachedSecondFamily parents source,
      (w (secondParentOf x)*actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
        slots₁ slots₂ (lists₁ (secondParentOf x)) (lists₂ (secondParentOf x)) a₁ a₂ W₁ W₂ Φ Y X := by
  rw [sum_attachedSecondFamily]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [secondExpansionSource_attached p hp hcop hg hinj hpr y (source y) (hE y hy)]
  rw [Finset.sum_image (fun x hx z hz he=>attachSecondExpansion_injective y he)]
  simp only [Finset.mul_sum,secondParentOf_attach]
  apply Finset.sum_congr rfl
  intro x hx
  ring

def parentPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (y : SecondParentSource ι Jo) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj pool (quotientSupport p y) y.cube.support
    (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (primeMark (slots\J) (residualLists p negative lists y) a) ω X
    (∏ i∈y.firstCommon,p i) (secondParentDivisor p y) core t Y

theorem parentPoisson_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    parentPoisson p hp hg hinj pool negative Ψ m slots J lists a ω X t Y r core (attach p J q)=
      priorityPoisson p hp hg hinj pool q.1.cube q.1.firstCommon negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) q.1.firstDivisor)
        slots J lists a ω X t Y r core q.1.quotientSupport := by
  unfold parentPoisson
  rw [quotientSupport_attach p hinj,residualLists_attach p hinj]
  rfl

def retainedRow (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0) : ℂ :=
  actualSecondSignedWeight p hp hcop hg Ψ
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
    actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
      (slots\J) (slots\J) (residualLists p negative lists (secondParentOf x))
      (residualLists p negative lists (secondParentOf x)) a a V V rowMajorant Y X

theorem parentPoisson_full [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (y : SecondParentSource ι Jo) (pool : Finset ι)
    (hq : y.quotient=sourceIdeal p (quotientSupport p y))
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    let V := principalWindow om lo hi hlo hs negative t
    let H := markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
    let K := secondVariableCutoff p y R
    parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y =
      truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K +
      (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
        (Y:ℂ)*secondRayCoefficient ray *
          ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
            retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
      secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K := by
  intro Ψ₀ V H K
  have hsum : (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          actualSecondSignedWeight p hp hcop hg Ψ₀
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ₀ m ray)
            (slots\J) (slots\J) (residualLists p negative lists y) (residualLists p negative lists y)
            a a V V rowMajorant Y X) =
    ∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x := by
    apply Finset.sum_congr rfl
    intro ray hray
    apply Finset.sum_congr rfl
    intro residual hresidual
    apply Finset.sum_congr rfl
    intro j hj
    apply congrArg ((Y:ℂ)*secondRayCoefficient ray * ·)
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    rfl
  have he := first_parent_full_second_source p hp hcop hg hinj hc hpr y pool (quotientSupport p y) hq
    negative (if negative then r.1 else r.2) Ψ m (slots\J) (residualLists p negative lists y) a
    (fun i _=>residualLists_disjoint p negative lists y i) om lo hi hlo hs X t Y hX hY core R label
  exact he.trans (congrArg (fun z : ℂ=>truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K + z +
    secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K) hsum)

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem retained_sum
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (w : SecondParentSource ι Jo→ℂ)
    (H : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ y∈parents,w y*∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y))
      residual (label y) j).image (attachSecondExpansion y),H x) =
    ∑ x∈retainedPool p pool parents R label residual j,w (secondParentOf x)*H x := by
  rw [retainedPool,sum_attachedSecondFamily]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_image (fun _ _ _ _ h=>attachSecondExpansion_injective y h),Finset.mul_sum]
  rfl

omit [DecidableEq ι] [DecidableEq κ] in
private theorem commute_parent_sectors [Fintype κ]
    (parents : Finset (SecondParentSource ι Jo)) (pool : Finset ι)
    (H : SecondParentSource ι Jo→SecondRayIndex→Finset ι→κ→ℂ) :
    (∑ y∈parents,∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,H y ray residual j) =
    ∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,∑ y∈parents,H y ray residual j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray hray
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro residual hresidual
  rw [Finset.sum_comm]

theorem parent_family_full [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (parents : Finset (SecondParentSource ι Jo)) (pool : Finset ι)
    (hq : ∀ y∈parents,y.quotient=sourceIdeal p (quotientSupport p y))
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : SecondParentSource ι Jo→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ) :
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    let V := principalWindow om lo hi hlo hs negative t
    let H := fun y=>markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
    let K := fun y=>secondVariableCutoff p y (R y)
    (∑ y∈parents,w y*parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y) =
    (∑ y∈parents,w y*truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) +
    (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈retainedPool p pool parents R label residual j,
          w (secondParentOf x)*retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
    (∑ y∈parents,w y*secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) := by
  intro Ψ₀ V H K
  have he : (∑ y∈parents,w y*parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y) =
    ∑ y∈parents,w y*(truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y) +
      (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
        (Y:ℂ)*secondRayCoefficient ray *
          ∑ x∈(secondDyadicSector pool (K y) residual (label y) j).image (attachSecondExpansion y),
            retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
      secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [parentPoisson_full p hp hcop hg hinj hc hpr y pool (hq y hy) negative Ψ m slots J lists a
      om lo hi hlo hs X t Y hX hY r core (R y) (label y)]
  rw [he]
  simp only [mul_add,Finset.sum_add_distrib]
  congr 1
  congr 1
  simp only [Finset.mul_sum]
  rw [commute_parent_sectors]
  apply Finset.sum_congr rfl
  intro ray hray
  apply Finset.sum_congr rfl
  intro residual hresidual
  apply Finset.sum_congr rfl
  intro j hj
  rw [retainedPool,sum_attachedSecondFamily]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_image (fun _ _ _ _ h=>attachSecondExpansion_injective y h)]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [secondParentOf_attach]
  ring

def fullSource [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (parents : Finset (SecondParentSource ι Jo)) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : SecondParentSource ι Jo→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ)
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ) : ℂ :=
  let H := fun y=>markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
  let K := fun y=>secondVariableCutoff p y (R y)
  (∑ y∈parents,w y*truncatedSecondZero p hg pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) +
  (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
    (Y:ℂ)*secondRayCoefficient ray *
      ∑ x∈retainedPool p pool parents R label residual j,
        w (secondParentOf x)*retainedRow p hp hcop hg pool negative Ψ m slots J lists a V X Y ray x) +
  (∑ y∈parents,w y*secondSourceTail p hp hg hinj pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y))

theorem first_priority_physical_source [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ) :
    (∑ D∈pool.powerset,
      priorityOuter p hg b negative Ψ m selector r core D *
      ‖primeMark J lists a (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2 *
      (priorityPoisson p hp hg hinj pool b C negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        slots J lists a om X t Y r core D).re) =
    (fullSource p hp hcop hg hinj
      (assignedParents p (fixedSource pool b C E old) negative J lists) pool negative
      (firstCoreTwist negative (if negative then r.1 else r.2) Ψ core) m slots J lists a
      (coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)))
      (principalWindow om lo hi hlo hs negative t) X Y R label).re := by
  rw [first_priority_physical_slice p hp hg hinj]
  have hfun (y : SecondParentSource ι (Jo+(J.card+J.card)))
      (hy : y∈assignedParents p (fixedSource pool b C E old) negative J lists) :
      parentFunction p (fun x=>priorityPoisson p hp hg hinj pool b C negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        slots J lists a om X t Y r core x.quotientSupport) (forgetAppended y) =
      parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y := by
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p _ negative J lists y).mp hy
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hx
    rw [forget_attach,parentFunction_parent p hinj,parentPoisson_attach p hp hg hinj]
    rfl
  have he := parent_family_full p hp hcop hg hinj hc hpr
    (assignedParents p (fixedSource pool b C E old) negative J lists) pool
    (fun y hy=>assigned_quotient p hinj _ negative J lists y hy)
    negative Ψ m slots J lists a
    (coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)))
    om lo hi hlo hs X t Y hX hY r core R label
  apply congrArg Complex.re
  calc
    _ = ∑ y∈assignedParents p (fixedSource pool b C E old) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hfun y hy]
    _ = _ := he

include hp in

theorem fixed_retained_conditions
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,∀ i,(old i).val∣sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p (retainedPool p pool
      (assignedParents p (fixedSource pool b C E old) negative J lists) R label residual j) := by
  apply retainedPool_conditions p hp
  intro x hx
  obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hx
  exact ⟨hb,hC,hE,hold D hD⟩

end SevenEighths.InversePrioritySecondSource

end

end OAI

end Source2500

/- Original source: OAI/NumberTheory/DirichletL/Descent/WholePriorityPhysical.lean; sha256: b3fca294d63ff4093a7a0364da57cd50ef8b83702a01cf87bad397b7f1a236a8 -/
section Source2501
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentWholePriorityPhysical
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InverseMomentWholePriorityParents InversePrioritySecondSource
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ] [Fintype κ]
variable {Jo : ℕ} (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def fullPhysical (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ)
    (y : SecondParentSource ι Jo) : ℂ :=
  let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
  let ll := fun i=>lists i\extra y.cube
  let H := markedRadial p (slots\J) (residualLists p negative ll y) a ∅ V X
  let K := secondVariableCutoff p y R
  truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K +
    (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ₀ m slots J ll a V X Y ray x) +
    secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K

theorem whole_parent_full
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ)
    (y : SecondParentSource ι Jo) (hq : y.quotient=sourceIdeal p (quotientSupport p y)) :
    parentPoisson p hp hg hinj pool negative Ψ m slots J
      (fun i=>lists i\extra y.cube) a om X t Y r core y =
    fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
      (principalWindow om lo hi hlo hs negative t) X Y r core R label y :=
  parentPoisson_full p hp hcop hg hinj hc hpr y pool hq negative Ψ m slots J
    (fun i=>lists i\extra y.cube) a om lo hi hlo hs X t Y hX hY r core R label

omit [DecidableEq σ] in
theorem whole_residual_lists_attach
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (q : Source ι Jo×((∀ i∈J,ι)×(∀ i∈J,ι))) :
    residualLists p negative (fun i=>lists i\extra (attach p J q).cube) (attach p J q)=
      fun i=>lists i\wholeExtractedSupport (fun x=>extra x.cube) negative q.1 := by
  rw [residualLists_attach p hinj]
  funext i
  ext k
  simp only [Finset.mem_sdiff,wholeExtractedSupport,Finset.mem_union]
  change (k ∈ lists i ∧ k ∉ extra q.1.cube) ∧ k ∉ extractedSupport negative q.1 ↔ _
  tauto

theorem whole_signed_source_full
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (source : Finset (Source ι Jo)) (w : Source ι Jo→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    (∑ x∈source,w x*(‖primeMark J lists a
      (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J
        (fun i=>lists i\extra x.cube) a om X t Y r core (parent p x)) =
    ∑ y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
      coefficient p J a w y *
        fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
          (principalWindow om lo hi hlo hs negative t) X Y r core R label y := by
  have he := wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj source negative J lists a w
    (fun y=>parentPoisson p hp hg hinj pool negative Ψ m slots J
      (fun i=>lists i\extra y.cube) a om X t Y r core y)
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro y hy
  obtain ⟨x,hx,q,hq,rfl⟩ :=
    (mem_wholeAssignedParents p (fun x=>extra x.cube) source negative J lists y).mp hy
  rw [forget_attach]
  apply congrArg (coefficient p J a w (attach p J (x,q))* ·)
  have hquot : (attach p J (x,q)).quotient=sourceIdeal p (quotientSupport p (attach p J (x,q))) := by
    rw [quotientSupport_attach p hinj];rfl
  exact whole_parent_full p hp hcop hg hinj hc hpr extra pool negative Ψ m slots J lists a
    om lo hi hlo hs X t Y hX hY r core R label (attach p J (x,q)) hquot

end SevenEighths.InverseMomentWholePriorityPhysical

end

end OAI

end Source2501

/- Original source: OAI/NumberTheory/DirichletL/Descent/PriorityProfile.lean; sha256: 2038392f6e188adced5fdec6bacfc5028a30c5b06726c939efd58c5993afde10 -/
section Source2502
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration
local notation "O" => ActualEisensteinCubic.O

def priorityLogWindow (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool):𝓢(ℝ,ℂ) :=
  if negative then conjugateProfile (CubicReflectionKernel.logSchwartz om a b ha hs (om.smooth ⊤))
  else CubicReflectionKernel.logSchwartz om a b ha hs (om.smooth ⊤)

def priorityHeight (negative:Bool) (t:ℝ):ℝ := if negative then -t else t

theorem priorityLogWindow_support (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool) :
    Function.support (priorityLogWindow om a b ha hs negative)⊆
      Set.Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro y hy
  have hn:om (Real.exp y)≠0:=by
    cases negative <;> simpa only [priorityLogWindow,Bool.false_eq_true,ite_true,ite_false,
      conjugateProfile_apply,CubicReflectionKernel.logSchwartz_apply,Function.mem_support,star_ne_zero] using hy
  have hh:=hs hn
  have hlo:=Real.log_le_log ha hh.1
  have hhi:=Real.log_le_log (Real.exp_pos y) hh.2
  rw [Real.log_exp] at hlo hhi
  constructor
  · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]

theorem principalWindow_positiveSource (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool) (t x:ℝ) (hx:0<x) :
    principalWindow om a b ha hs negative t x =
      positiveSource (priorityLogWindow om a b ha hs negative) 1 (priorityHeight negative t) x := by
  rw [principalWindow_apply]
  cases negative <;> simp only [priorityLogWindow,priorityHeight,Bool.false_eq_true,ite_true,ite_false,
    positiveSource,Real.log_one,add_zero,conjugateProfile_apply,CubicReflectionKernel.logSchwartz_apply,
    Real.exp_log hx,normTwistedSource]

theorem positiveSource_conjugate_one (g:𝓢(ℝ,ℂ)) (t x:ℝ) :
    star (positiveSource (conjugateProfile g) 1 (-t) x)=positiveSource g 1 t x := by
  simp only [positiveSource,Real.log_one,add_zero,conjugateProfile_apply,star_mul,star_star,
    logPhase_conjugate,neg_neg,mul_comm]

theorem actualSecondProfileRow_congr_positive {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι) (x:SecondProfileData ι) (slots₁ slots₂:Finset σ)
    (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (W₁ W₂ V₁ V₂:ℝ→ℂ) (Φ:𝓢(ℝ,ℂ)) (Y X:ℝ) (hX:0<X)
    (h₁:∀t,0<t→W₁ t=V₁ t) (h₂:∀t,0<t→W₂ t=V₂ t) :
    actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X =
      actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂ V₁ V₂ Φ Y X := by
  simp only [actualSecondProfileRow_eq_whole p hp hcop hg]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  congr 1
  unfold secondNormProfile
  have h0 : secondActualNorms p x N M 0 = primeProductNorm p x.common := rfl
  have h2 : secondActualNorms p x N M 2 = primeProductNorm p x.overlap := rfl
  have h4 : secondActualNorms p x N M 4 = primeProductNorm p N := rfl
  have h5 : secondActualNorms p x N M 5 = primeProductNorm p M := rfl
  rw [h0,h2,h4,h5]
  dsimp only
  rw [h₁ _ (div_pos (mul_pos (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
      (primeProductNorm_pos p hp _)) hX),
    h₂ _ (div_pos (mul_pos (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
      (primeProductNorm_pos p hp _)) hX)]

theorem actual_priority_profile_common {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι) (x:SecondProfileData ι) (slots₁ slots₂:Finset σ)
    (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (negative:Bool) (t:ℝ) (Φ:𝓢(ℝ,ℂ)) (Y X:ℝ) (hX:0<X) :
    let g:=priorityLogWindow om lo hi hlo hs negative
    let θ:=priorityHeight negative t
    actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
      (principalWindow om lo hi hlo hs negative t) (principalWindow om lo hi hlo hs negative t) Φ Y X =
      actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
        (fun y=>star (positiveSource (conjugateProfile g) 1 (-θ) y)) (positiveSource g 1 θ) Φ Y X := by
  intro g θ
  apply actualSecondProfileRow_congr_positive p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
    _ _ _ _ Φ Y X hX
  · intro y hy
    rw [positiveSource_conjugate_one]
    exact principalWindow_positiveSource om lo hi hlo hs negative t y hy
  · intro y hy
    exact principalWindow_positiveSource om lo hi hlo hs negative t y hy

end SevenEighths.InverseMoment

end

end OAI

end Source2502

/- Original source: OAI/NumberTheory/DirichletL/Descent/WholeRetainedSource.lean; sha256: 9f12500e51e986f3b82b2273ac400325ef3c9014071443cf4de831b388ae5489 -/
section Source2503
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMomentWholeRetainedSource
open ActualEisensteinCubic SecondPassArithmetic InverseMoment InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentWholePriorityParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def deleted (extra : CubeCoordinates ι→Finset ι) (negative : Bool)
    (x : MarkedSecondSource ι Jo 0) : Finset ι :=
  extra x.cube∪(((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪
    quotientSupport p (secondParentOf x))

theorem retained_conditions (hp : ∀ i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (hextra : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p
      (retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists)
        R label residual j) := by
  apply whole_assigned_family_conditions p hp (fun x=>extra x.cube) source hs hextra negative J lists
  intro y hy x hx
  exact (second_variable_original_support p y pool residual (R y) (label y) j x hx).2.1

theorem retained_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (hextra : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists)
      R label residual j) :
    ∀ i∈deleted p extra negative x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient := by
  have hy := ((mem_retainedPool p pool _ R label residual j x).mp hx).1
  obtain ⟨s,hs₀,q,hq,he⟩ := (mem_wholeAssignedParents p (fun x=>extra x.cube) source negative J lists _).mp hy
  have hc : x.cube=s.cube := (congrArg SecondParentSource.cube he).symm
  have hC : x.firstCommon=s.firstCommon := (congrArg SecondParentSource.firstCommon he).symm
  have ht : x.quotient=sourceIdeal p s.quotientSupport := (congrArg SecondParentSource.quotient he).symm
  have hqs : quotientSupport p (secondParentOf x)=s.quotientSupport := by
    rw [←he,quotientSupport_attach p hinj]
  intro i hi
  change i∈extra x.cube∪(((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪
    quotientSupport p (secondParentOf x)) at hi
  rw [hc,hC,hqs] at hi
  rcases Finset.mem_union.mp hi with hi|hi
  · exact Or.inl (Finset.mem_union_left _ (hc.symm ▸ hextra s hs₀ hi))
  · rcases Finset.mem_union.mp hi with hi|hi
    · left
      rw [hc,hC]
      rcases Finset.mem_union.mp hi with hi|hi
      · apply Finset.mem_union_left
        cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hi
        · exact (hs s hs₀).admissible.1 hi
        · exact (hs s hs₀).admissible.2 hi
      · exact Finset.mem_union_right _ hi
    · right
      rw [ht]
      exact source_prime_dvd p _ i hi

theorem whole_coefficient_norm
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (B : ℝ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1) (hw : ∀ x∈source,‖w x‖≤B)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈wholeAssignedParents p extra source negative J lists) :
    ‖coefficient p J a w y‖≤B := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
  rw [coefficient_attach p hinj,norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pairedSlotWeight_norm_le_one J J lists lists a a
    _ q hq ha ha)).trans (hw x hx)

end SevenEighths.InverseMomentWholeRetainedSource

end

end OAI

end Source2503

/- Original source: OAI/NumberTheory/DirichletL/Inversion/SecondSourceBlocks.lean; sha256: 7825728e6109d920bcceff7b7712a075829da6338cd82dfa6d8ad0389be78a68 -/
section Source2504
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseSecondSourceBlocks
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseMoment
open InverseSecondFibers InversePrioritySecondSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]

abbrev BlockIndex := Fin 4 → ℕ

def outerNorms (p : ι → O) {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Fin 4 → ℝ :=
  ![primeProductNorm p x.second.sourceCommon, primeProductNorm p x.second.divisor,
    primeProductNorm p x.second.overlap, ‖eisEmbedding x.second.frequency‖^2]

theorem outerNorms_eq_actual (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (Ψ : O →* ℂ) (m : O)
    (ray : SecondRayIndex) (N M : Finset ι) (i : Fin 4) :
    outerNorms p x i = secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i) := by
  fin_cases i <;> simp [outerNorms,secondActualNorms,secondInheritedProfile,
    actualMarkedSecondProfileData,expansionProfileData,primeSubsetGenerator_norm_eq_productNorm]

omit [DecidableEq ι] in
theorem outerNorms_ge_one (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hk : x.second.frequency ≠ 0) :
    ∀ i,1 ≤ outerNorms p x i := by
  intro i
  fin_cases i
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact element_norm_ge_one _ hk

theorem frequency_ne_zero_of_gate (a : O) (R : ℝ) {k : O}
    (hk : k ∈ nonzeroChildFrequencyBall a R) : k ≠ 0 :=
  (Finset.mem_erase.mp hk).1

theorem retained_frequency_ne_zero (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo → Finset ι → Finset ι → ℝ)
    (label : SecondParentSource ι Jo → Finset ι → SecondExpansionData ι → κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι Jo 0)
    (hx : x ∈ retainedPool p pool parents R label residual j) : x.second.frequency ≠ 0 :=
  frequency_ne_zero_of_gate _ _ (retainedPool_original_support p pool parents R label residual j x hx).2.2.2

def dyadIndex (r : ℝ) : ℕ := ⌊Real.logb 2 r⌋₊
def dyadScale (n : ℕ) : ℝ := 2^n

theorem dyadScale_pos (n : ℕ) : 0 < dyadScale n := by unfold dyadScale; positivity

theorem dyadIndex_bounds (r : ℝ) (hr : 1 ≤ r) :
    dyadScale (dyadIndex r) ≤ r ∧ r < 2*dyadScale (dyadIndex r) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlog : 0 ≤ Real.logb 2 r := Real.logb_nonneg (by norm_num) hr
  constructor
  · have h := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hr0).mp (Nat.floor_le hlog)
    simpa only [dyadScale,dyadIndex,Real.rpow_natCast] using h
  · have h := (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hr0).mp
      (Nat.lt_floor_add_one (Real.logb 2 r))
    have ht : r < (2:ℝ)^(dyadIndex r+1) := by
      rw [←Real.rpow_natCast]
      simpa only [Nat.cast_add,Nat.cast_one,dyadIndex] using h
    simpa only [dyadScale,pow_succ,mul_comm] using ht

def index (p : ι → O) {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : BlockIndex :=
  fun i => dyadIndex (outerNorms p x i)

def keys (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) : Finset BlockIndex :=
  source.image (index p)

def cell (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : Finset (MarkedSecondSource ι Jo Jn) := source.filter (fun x => index p x = d)

omit [DecidableEq ι] in
@[simp] theorem mem_cell (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) :
    x ∈ cell p source d ↔ x ∈ source ∧ index p x = d := Finset.mem_filter

omit [DecidableEq ι] in
theorem cell_subset (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : cell p source d ⊆ source := Finset.filter_subset _ _

omit [DecidableEq ι] in
theorem cell_inherits (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (P : MarkedSecondSource ι Jo Jn → Prop) (hP : ∀ x∈source,P x) :
    ∀ x∈cell p source d,P x := fun x hx => hP x (cell_subset p source d hx)

theorem cell_conditions (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex) :
    ActualSecondSourceConditions p (cell p source d) := ActualSecondSourceConditions.mono p hs (cell_subset p source d)

omit [DecidableEq ι] in
theorem mem_keys_iff (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : d ∈ keys p source ↔ (cell p source d).Nonempty := by
  simp only [keys,Finset.mem_image,Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨x,hx,he⟩
    exact Finset.nonempty_iff_ne_empty.mp ⟨x,(mem_cell p source d x).mpr ⟨hx,he⟩⟩
  · intro h
    obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr h
    exact ⟨x,(mem_cell p source d x).mp hx⟩

omit [DecidableEq ι] in
theorem cells_disjoint (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    {d e : BlockIndex} (h : d ≠ e) : Disjoint (cell p source d) (cell p source e) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h (((mem_cell p source d x).mp hx).2.symm.trans ((mem_cell p source e x).mp hy).2)

omit [DecidableEq ι] in
theorem cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (i : Fin 4) :
    1 ≤ outerNorms p x i / dyadScale (d i) ∧ outerNorms p x i / dyadScale (d i) < 2 := by
  obtain ⟨hxs,he⟩ := (mem_cell p source d x).mp hx
  have hb := dyadIndex_bounds _ (outerNorms_ge_one p hp x (hk x hxs) i)
  have hi : dyadIndex (outerNorms p x i) = d i := congrFun he i
  rw [hi] at hb
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hb.1),
    (div_lt_iff₀ (dyadScale_pos _)).mpr hb.2⟩

omit [DecidableEq ι] in
theorem sum_cells (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    {β : Type*} [AddCommMonoid β] (f : MarkedSecondSource ι Jo Jn → β) :
    (∑ x∈source,f x) = ∑ d∈keys p source,∑ x∈cell p source d,f x := by
  exact (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (index p) hx) f).symm

def scales (d : BlockIndex) : Fin 4 → ℝ := fun i => dyadScale (d i)

theorem actual_cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (N M : Finset ι) (i : Fin 4) :
    1 ≤ secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i) / scales d i ∧
    secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i) / scales d i < 2 := by
  rw [←outerNorms_eq_actual p x Ψ m ray N M i]
  exact cell_ratios p hp source hk d x hx i

theorem physical_source_partition
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0 → Finset ι)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    (Y:ℂ)*secondRayCoefficient ray *
      (∑ x∈source,(w x * actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x) *
        actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x)
          a₁ a₂ W₁ W₂ Φ Y X) =
    ∑ d∈keys p source,(Y:ℂ)*secondRayCoefficient ray *
      (∑ x∈cell p source d,(w x * actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x) *
        actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x)
          a₁ a₂ W₁ W₂ Φ Y X) := by
  rw [sum_cells p source]
  exact Finset.mul_sum _ _ _

def capBox (A : Fin 4 → ℝ) (Z : ℝ) : Finset BlockIndex :=
  Fintype.piFinset (fun i => Finset.range (dyadIndex (Z^(A i))+1))

omit [DecidableEq ι] in
theorem keys_subset_capBox (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (A : Fin 4 → ℝ) (Z : ℝ) (hcaps : ∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) :
    keys p source ⊆ capBox A Z := by
  intro d hd
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hd
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact Nat.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (lt_of_lt_of_le zero_lt_one (outerNorms_ge_one p hp x (hk x hx) i)) (hcaps x hx i))

omit [DecidableEq ι] in
theorem keys_card_le_product (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (A : Fin 4 → ℝ) (Z : ℝ) (hcaps : ∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) :
    (keys p source).card ≤ ∏ i : Fin 4,(dyadIndex (Z^(A i))+1) := by
  have h := Finset.card_le_card (keys_subset_capBox p hp source hk A Z hcaps)
  simpa [capBox,Fintype.card_piFinset] using h

def capConstant (A : Fin 4 → ℝ) : ℝ := (∑ i,A i)/Real.log 2

theorem capConstant_nonneg (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) :
    0 ≤ capConstant A := by
  unfold capConstant
  exact div_nonneg (Finset.sum_nonneg (fun i _ => hA i)) (Real.log_pos (by norm_num)).le

theorem cap_bin_bound (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) (Z : ℝ) (hZ : 2 ≤ Z)
    (i : Fin 4) : (dyadIndex (Z^(A i)) : ℝ)+1 ≤ 1+capConstant A*Real.log Z := by
  have hZ0 : 0 < Z := by linarith
  have hZi : 1 ≤ Z^(A i) := Real.one_le_rpow (by linarith) (hA i)
  have hf := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hZi)
  have hAi : A i ≤ ∑ j,A j := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  have hc := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hAi
    (Real.log_pos (by norm_num : (1:ℝ)<2)).le) (Real.log_nonneg (by linarith : 1 ≤ Z))
  dsimp [dyadIndex,capConstant]
  calc
    _ ≤ 1+Real.logb 2 (Z^(A i)) := by linarith
    _ = 1+(A i/Real.log 2)*Real.log Z := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos hZ0,Real.logb]
      ring
    _ ≤ _ := by linarith

omit [DecidableEq ι] in
theorem keys_card_polynomial (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → O) (_hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
      (source : Finset (MarkedSecondSource ι Jo Jn)) (Z : ℝ), 2 ≤ Z →
      (∀ x∈source,x.second.frequency ≠ 0) →
      (∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) →
      ((keys p source).card : ℝ) ≤ (1+C*Real.log Z)^4 := by
  refine ⟨capConstant A,capConstant_nonneg A hA,?_⟩
  intro p hp _ Jo Jn source Z hZ hk hcaps
  have h := keys_card_le_product p hp source hk A Z hcaps
  have hr : ((keys p source).card:ℝ) ≤ ∏ i : Fin 4,((dyadIndex (Z^(A i)):ℝ)+1) := by
    exact_mod_cast h
  apply hr.trans
  calc
    _ ≤ ∏ _i : Fin 4,(1+capConstant A*Real.log Z) :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => cap_bin_bound A hA Z hZ i)
    _ = (1+capConstant A*Real.log Z)^4 := by simp

omit [DecidableEq ι] in
@[simp] theorem keys_empty (p : ι → O) (Jo Jn : ℕ) :
    keys p (∅ : Finset (MarkedSecondSource ι Jo Jn)) = ∅ := by simp [keys]

omit [DecidableEq ι] in
@[simp] theorem cell_empty (p : ι → O) (Jo Jn : ℕ) (d : BlockIndex) :
    cell p (∅ : Finset (MarkedSecondSource ι Jo Jn)) d = ∅ := by simp [cell]

omit [DecidableEq ι] in
theorem cell_empty_of_not_mem (p : ι → O) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (d : BlockIndex) (hd : d ∉ keys p source) :
    cell p source d = ∅ := by
  exact Finset.not_nonempty_iff_eq_empty.mp (fun h => hd ((mem_keys_iff p source d).mpr h))

theorem retained_cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ}
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo → Finset ι → Finset ι → ℝ)
    (label : SecondParentSource ι Jo → Finset ι → SecondExpansionData ι → κ)
    (residual : Finset ι) (j : κ) (d : BlockIndex) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈cell p (retainedPool p pool parents R label residual j) d)
    (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (N M : Finset ι) (i : Fin 4) :
    1 ≤ secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i)/scales d i ∧
    secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i)/scales d i < 2 :=
  actual_cell_ratios p hp _ (retained_frequency_ne_zero p pool parents R label residual j)
    d x hx Ψ m ray N M i

theorem retained_keys_card_polynomial (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → O) (_hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ}
      (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
      (R : SecondParentSource ι Jo → Finset ι → Finset ι → ℝ)
      (label : SecondParentSource ι Jo → Finset ι → SecondExpansionData ι → κ)
      (residual : Finset ι) (j : κ) (Z : ℝ), 2 ≤ Z →
      (∀ x∈retainedPool p pool parents R label residual j,∀ i,outerNorms p x i ≤ Z^(A i)) →
      ((keys p (retainedPool p pool parents R label residual j)).card:ℝ) ≤
        (1+C*Real.log Z)^4 := by
  obtain ⟨C,hC,h⟩ := keys_card_polynomial (ι:=ι) A hA
  refine ⟨C,hC,?_⟩
  intro p hp _ Jo pool parents R label residual j Z hZ hcaps
  exact h p hp _ Z hZ (retained_frequency_ne_zero p pool parents R label residual j) hcaps

end SevenEighths.InverseSecondSourceBlocks

end

end OAI

end Source2504

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondCellPhysical.lean; sha256: 5f11f079f29bfe28a42a85babf8c29011f0cae038e23d32d3d9045b07456777a -/
section Source2505
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration
local notation "O" => ActualEisensteinCubic.O

def secondCellColumnExponent (Z X:ℝ) (d:BlockIndex):ℝ :=
  Real.logb Z (X/(scales d 0*scales d 2))

theorem second_cell_column_scale (Z X:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X) :
    Z^(secondCellColumnExponent Z X d)=X/(scales d 0*scales d 2) := by
  exact Real.rpow_logb (by linarith) (ne_of_gt hZ)
    (div_pos hX (mul_pos (dyadScale_pos _) (dyadScale_pos _)))

theorem second_cell_physical_scale (Z X:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X) :
    scales d 0*scales d 2*Z^(secondCellColumnExponent Z X d)=X := by
  rw [second_cell_column_scale Z X d hZ hX]
  field_simp [scales,ne_of_gt (dyadScale_pos (d 0)),ne_of_gt (dyadScale_pos (d 2))]

theorem second_cell_clipping_ratio (Z X b:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X)
    (hb:1≤b) (hsource:scales d 0*scales d 2≤b*X) :
    1≤Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d) ∧
    Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d)≤b := by
  let N:=secondCellColumnExponent Z X d
  have hz:0<Z:=lt_trans zero_lt_one hZ
  have hn:Z^N=X/(scales d 0*scales d 2):=second_cell_column_scale Z X d hZ hX
  constructor
  · exact Real.one_le_rpow hZ.le (sub_nonneg.mpr (le_max_right _ _))
  · by_cases hN:0≤N
    · rw [max_eq_right hN,sub_self,Real.rpow_zero];exact hb
    · have hN':N≤0:=le_of_not_ge hN
      rw [max_eq_left hN',zero_sub,Real.rpow_neg hz.le,hn,inv_div]
      exact (div_le_iff₀ hX).mpr hsource

theorem actual_priority_cell_profile {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι) (x:SecondProfileData ι) (slots₁ slots₂:Finset σ)
    (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (negative:Bool) (t:ℝ) (Φ:𝓢(ℝ,ℂ)) (Y X Z:ℝ) (hX:0<X) (hZ:1<Z) (d:BlockIndex) :
    let g:=priorityLogWindow om lo hi hlo hs negative
    let θ:=priorityHeight negative t
    actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
      (principalWindow om lo hi hlo hs negative t) (principalWindow om lo hi hlo hs negative t) Φ Y X =
      actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
        (fun y=>star (positiveSource (conjugateProfile g) 1 (-θ) y)) (positiveSource g 1 θ) Φ Y
        (scales d 0*scales d 2*Z^(secondCellColumnExponent Z X d)) := by
  rw [second_cell_physical_scale Z X d hZ hX]
  exact actual_priority_profile_common p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
    om lo hi hlo hs negative t Φ Y X hX

theorem actual_priority_cells {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo:ℕ} (source:Finset (MarkedSecondSource ι Jo 0))
    (pool:Finset ι) (Ψ:O→*ℂ) (m:O) (ray:SecondRayIndex)
    (slots₁ slots₂:Finset σ) (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (deleted₁ deleted₂:MarkedSecondSource ι Jo 0→Finset ι)
    (w:MarkedSecondSource ι Jo 0→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (negative:Bool) (t:ℝ) (Φ:𝓢(ℝ,ℂ)) (Y X Z:ℝ) (hX:0<X) (hZ:1<Z) :
    let g:=priorityLogWindow om lo hi hlo hs negative
    let θ:=priorityHeight negative t
    (Y:ℂ)*secondRayCoefficient ray *
      (∑x∈source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x)*
        actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
          (principalWindow om lo hi hlo hs negative t) (principalWindow om lo hi hlo hs negative t) Φ Y X) =
    ∑d∈keys p source,(Y:ℂ)*secondRayCoefficient ray *
      (∑x∈cell p source d,(w x*actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x)*
        actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
          (fun y=>star (positiveSource (conjugateProfile g) 1 (-θ) y)) (positiveSource g 1 θ) Φ Y
          (scales d 0*scales d 2*Z^(secondCellColumnExponent Z X d))) := by
  intro g θ
  refine (physical_source_partition p hp hcop hg source pool Ψ m ray slots₁ slots₂ lists₁ lists₂
    a₁ a₂ deleted₁ deleted₂ w (principalWindow om lo hi hlo hs negative t)
    (principalWindow om lo hi hlo hs negative t) Φ Y X).trans ?_
  apply Finset.sum_congr rfl
  intro d hd
  apply congrArg ((Y : ℂ) * secondRayCoefficient ray * ·)
  apply Finset.sum_congr rfl
  intro x hx
  exact congrArg ((w x * actualSecondSignedWeight p hp hcop hg Ψ
    (m * ConcretePrimeRowBridge.idealGenerator x.quotient) ray x) * ·)
    (actual_priority_cell_profile p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
      slots₁ slots₂ _ _ a₁ a₂ om lo hi hlo hs negative t Φ Y X Z hX hZ d)

theorem actual_source_block_ratios {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn)) (d:BlockIndex)
    (hcell:∀x∈source,index p x=d) (hk:∀x∈source,x.second.frequency≠0) :
    ∀x∈source,∀i,InverseSecondChildWindows.actualOuterRatios p x
      (scales d 0) (scales d 1) (scales d 2) (scales d 3) i∈Set.Icc 1 2 := by
  intro x hx i
  have hxcell:x∈cell p source d:=(mem_cell p source d x).mpr ⟨hx,hcell x hx⟩
  have hr:=cell_ratios p hp source hk d x hxcell i
  have he:InverseSecondChildWindows.actualOuterRatios p x
      (scales d 0) (scales d 1) (scales d 2) (scales d 3) i=outerNorms p x i/scales d i := by
    fin_cases i <;> simp [InverseSecondChildWindows.actualOuterRatios,outerNorms,
      primeSubsetGenerator_norm_eq_productNorm]
  rw [he]
  exact ⟨hr.1,hr.2.le⟩

end SevenEighths.InverseMoment

end

end OAI

end Source2505

/- Original source: OAI/NumberTheory/DirichletL/Descent/PriorityCellEnergy.lean; sha256: 313a8e4864f94ca26ab6bc12716914a0ed9dc73da1154b0841f9b4862546fb83 -/
section Source2506
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_cell_recursive
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (Aker J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source) (d:InverseSecondSourceBlocks.BlockIndex)
    (_hcell:∀x∈source,InverseSecondSourceBlocks.index p x=d),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y R L Z X Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ x∈source,primeProductNorm p x.second.sourceCommon ≤ Z^(gcount+eta)) →
      (∀ x∈source,Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+Vlabel) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+Vlabel) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^Aker)) := by
  let g:=priorityLogWindow om lo hi hlo hsupport negative
  let mg:=|Real.log lo|+|Real.log hi|
  have hm:0≤mg:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hg:Function.support g⊆Set.Icc (-mg) mg:=priorityLogWindow_support om lo hi hlo hsupport negative
  have hcg:Function.support (conjugateProfile g)⊆Set.Icc (-mg) mg:=by
    intro x hx
    apply hg
    simpa only [Function.mem_support,conjugateProfile_apply,star_ne_zero] using hx
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,henergy⟩:=
    actual_second_fixed_block_recursive (ι:=ι) (σ:=σ) (conjugateProfile g) g Φ mg mg 1
      (fun _=>1) (fun _=>2) B₀ hm hm (le_refl 1) (fun _=>zero_lt_one)
      (fun _=>by norm_num) hB₀ hcg hg Aker J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,?_⟩
  intro p hp _ hcop hg₀ hpr hinj hc Jo source hs d hcell pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X Vlabel εchild ell Ractive j tcount gcount theta eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY hrows hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hblock:=actual_source_block_ratios p hp source d hcell
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx))
  have he:=henergy p hp hcop hg₀ hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    (scales d 0) (scales d 1) (scales d 2) (scales d 3) Y R L Z
    (secondCellColumnExponent Z X d) Vlabel εchild ell Ractive j tcount gcount theta eta ρ
    1 1 (-priorityHeight negative t) (priorityHeight negative t) w labels A
    hd₁ hd₂ hρ (le_refl 1) (le_refl 1) (le_refl 1) (le_refl 1) hL (lt_trans zero_lt_one hZ)
    (dyadScale_pos _) (dyadScale_pos _) (dyadScale_pos _) (dyadScale_pos _)
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one hZ) _) hY hrows hblock
    hcube₁ hcube₂ hactive hj hquot hcommon hdiv hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  rw [second_cell_physical_scale Z X d hZ hX] at he
  refine le_trans (le_of_eq (congrArg (fun v : ℂ => ‖(Y : ℂ) * secondRayCoefficient z * v‖) ?_)) he
  apply Finset.sum_congr rfl
  intro x _hx
  exact congrArg (fun v : ℂ => (w x * actualSecondSignedWeight p hp hcop hg₀ Ψ
    (m * ConcretePrimeRowBridge.idealGenerator x.quotient) z x) * v)
    (actual_priority_profile_common p hp hcop hg₀ pool (secondInheritedProfile p x Ψ m z)
      slots₁ slots₂ _ _ a₁ a₂ om lo hi hlo hsupport negative t Φ Y X hX)

end SevenEighths.InverseMoment

end

end OAI

end Source2506

/- Original source: OAI/NumberTheory/DirichletL/Descent/PhysicalBlockBudget.lean; sha256: 20ecdfadef291316fe02384873a24f8749b0b1b2a3c45f57c07c367e783cb3e5 -/
section Source2507
namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

theorem second_source_scalar_norm (Y E V X : ℝ)
    (hY : 0<Y) (hE : 0<E) (hV : 0<V) (hX : 0<X) (a : ℂ) :
    ‖(Y:ℂ)*a*((E*V*X:ℝ):ℂ)⁻¹‖ = ‖a‖*(Y/(E*V*X)) := by
  rw [norm_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,abs_of_pos (by positivity : 0<E*V*X)]
  ring

theorem physical_block_rpow_budget
    (Z : ℝ) (hZ : 1≤Z) (M r ell V δ A B R j t g θ v η τ π ε εmass : ℝ)
    (hclip : max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v≤6*η)
    (hεmass : εmass*(secondCount ell R j t g θ+11*η/2)≤π) :
    Z^(firstKappa M r ell V δ A B R) * Real.exp ((9/2:ℝ)*(η*Real.log Z)) *
      (Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ) /
        (Z^θ*Z^v*Z^(secondFormalColumn r A B t g v)) * Real.exp (6*(η*Real.log Z))) *
      Z^((secondCount ell R j t g θ+11*η/2)*(1+εmass)) *
      Z^(2*(max 0 (secondFormalColumn r A B t g v)+secondFormalLabel B θ v j)+ε) ≤
    Z^(r+3*ell+V+40*η+τ+π+ε) := by
  have hZpos : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [second_physical_scalar Z hZpos]
  have hexp : Real.exp ((9/2:ℝ)*(η*Real.log Z))=Z^((9/2:ℝ)*η) := by
    rw [Real.rpow_def_of_pos hZpos]
    congr 1
    ring
  rw [hexp,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hb := physical_step_energy_exponent M r ell V δ A B R j t g θ v η τ π ε
    (max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v) hclip
  nlinarith

theorem physical_block_scalar_budget
    (Z : ℝ) (hZ : 1≤Z) (M r ell V δ A B R j t g θ v η τ π ε εmass : ℝ)
    (ray : ℂ) (C : ℝ) (hC : 0≤C)
    (hclip : max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v≤6*η)
    (hεmass : εmass*(secondCount ell R j t g θ+11*η/2)≤π) :
    C * Z^(firstKappa M r ell V δ A B R) * Real.exp ((9/2:ℝ)*(η*Real.log Z)) *
      (Real.exp (6*(η*Real.log Z)) *
        ‖((Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ):ℝ):ℂ)*ray*
          ((Z^θ*Z^v*Z^(secondFormalColumn r A B t g v):ℝ):ℂ)⁻¹‖) *
      Z^((secondCount ell R j t g θ+11*η/2)*(1+εmass)) *
      Z^(2*(max 0 (secondFormalColumn r A B t g v)+secondFormalLabel B θ v j)+ε) ≤
    C*‖ray‖*Z^(r+3*ell+V+40*η+τ+π+ε) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [second_source_scalar_norm _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)]
  have hh := mul_le_mul_of_nonneg_left
    (physical_block_rpow_budget Z hZ M r ell V δ A B R j t g θ v η τ π ε εmass hclip hεmass)
    (mul_nonneg hC (norm_nonneg ray))
  convert hh using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI

end Source2507

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondCellParameters.lean; sha256: 9dad1544ee2f7a81b7a374b6855b9f05b5b32f82dc107e175190dc22ca4136ff -/
section Source2508
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseInitialArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def secondCellExponent (Z:ℝ) (d:BlockIndex) (i:Fin 4):ℝ:=Real.logb Z (scales d i)

theorem secondCellExponent_nonneg (Z:ℝ) (d:BlockIndex) (i:Fin 4) (hZ:1<Z):
    0≤secondCellExponent Z d i := by
  apply Real.logb_nonneg hZ
  exact one_le_pow₀ (by norm_num : (1:ℝ)≤2)

theorem second_cell_scale_rpow (Z:ℝ) (d:BlockIndex) (i:Fin 4) (hZ:1<Z):
    Z^(secondCellExponent Z d i)=scales d i :=
  Real.rpow_logb (by linarith) (ne_of_gt hZ) (dyadScale_pos _)

theorem second_cell_formal_column (Z r A B t:ℝ) (d:BlockIndex) (hZ:1<Z):
    secondCellColumnExponent Z (Z^(r-A-B-t)) d=
      secondFormalColumn r A B t (secondCellExponent Z d 0) (secondCellExponent Z d 2) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  apply (Real.rpow_right_inj hz (ne_of_gt hZ)).mp
  rw [second_cell_column_scale Z _ d hZ (Real.rpow_pos_of_pos hz _)]
  rw [←second_cell_scale_rpow Z d 0 hZ,←second_cell_scale_rpow Z d 2 hZ,
    ←Real.rpow_add hz,←Real.rpow_sub hz]
  congr 1
  unfold secondFormalColumn
  ring

theorem actual_second_child_label_norm {ι:Type*} [DecidableEq ι]
    (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (x:MarkedSecondSource ι Jo Jn) (u v:Oˣ):
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)=
      ‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*primeProductNorm p x.second.divisor*
      primeProductNorm p x.second.overlap := by
  have hn(S:Finset ι):(Ideal.absNorm (sourceIdeal p S):ℝ)=primeProductNorm p S:=by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏i∈S,p i)).symm
  change (Ideal.absNorm (Ideal.span {jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} *
      sourceIdeal p x.firstCommon * sourceIdeal p x.second.divisor * sourceIdeal p x.second.overlap):ℝ)=_
  simp only [map_mul,Nat.cast_mul,hn,←eisEmbedding_norm_sq_eq_absNorm_span]

theorem actual_cell_child_label_bound {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (hk:∀x∈source,x.second.frequency≠0) (d:BlockIndex)
    (x:MarkedSecondSource ι Jo Jn) (hx:x∈cell p source d) (u v:Oˣ):
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤
      4*‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*scales d 1*scales d 2 := by
  have hE:= (cell_ratios p hp source hk d x hx 1).2.le
  have hV:= (cell_ratios p hp source hk d x hx 2).2.le
  have he:primeProductNorm p x.second.divisor≤2*scales d 1:=
    (div_le_iff₀ (dyadScale_pos _)).mp hE
  have hv:primeProductNorm p x.second.overlap≤2*scales d 2:=
    (div_le_iff₀ (dyadScale_pos _)).mp hV
  rw [actual_second_child_label_norm]
  calc
    _ ≤ ‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*(2*scales d 1)*(2*scales d 2) := by
      have hc0 := (primeProductNorm_pos p hp x.firstCommon).le
      have hv0 := (primeProductNorm_pos p hp x.second.overlap).le
      have hs0 := (dyadScale_pos (d 1)).le
      gcongr
    _ = _ := by ring

theorem actual_cell_child_label_power {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (hk:∀x∈source,x.second.frequency≠0) (d:BlockIndex)
    (x:MarkedSecondSource ι Jo Jn) (hx:x∈cell p source d) (u v:Oˣ)
    (Z B j eta:ℝ) (hZ:1<Z) (hbin:2≤Z^eta)
    (hC:primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ:‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤
      Z^(secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hfour:(4:ℝ)≤Z^(2*eta):=by
    have hh:=mul_le_mul hbin hbin (by norm_num) (Real.rpow_nonneg hz.le _)
    norm_num only [←Real.rpow_add hz,show eta+eta=2*eta by ring] at hh
    exact hh
  apply (actual_cell_child_label_bound p hp source hk d x hx u v).trans
  calc
    _≤Z^(2*eta)*Z^(j+eta)*Z^(B+eta)*scales d 1*scales d 2:=by
      have hc0:0≤primeProductNorm p x.firstCommon:=(primeProductNorm_pos p hp _).le
      have hs1:0≤scales d 1:=(dyadScale_pos _).le
      have hs2:0≤scales d 2:=(dyadScale_pos _).le
      gcongr
    _= _:=by
      rw [←second_cell_scale_rpow Z d 1 hZ,←second_cell_scale_rpow Z d 2 hZ,
        ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1
      unfold secondFormalLabel
      ring

theorem second_cell_clipping_width (Z X b eta:ℝ) (d:BlockIndex)
    (hZ:1<Z) (hX:0<X) (hb:1≤b)
    (hsource:scales d 0*scales d 2≤b*X) (hthreshold:b≤Z^(6*eta)) :
    max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d≤6*eta := by
  exact (Real.rpow_le_rpow_left_iff hZ).mp
    ((second_cell_clipping_ratio Z X b d hZ hX hb hsource).2.trans hthreshold)

end SevenEighths.InverseMoment

end

end OAI

end Source2508

/- Original source: OAI/NumberTheory/DirichletL/Descent/PriorityMovingRadius.lean; sha256: 2045718c9a67d7fdbba77281101114894cea7b06be7e6a875769e39d6d9eef7d -/
section Source2509
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_source_moving_radius
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      ∑d∈keys p source,(Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+(Vlabel d))+εchild))*
          Z^((ell+Ractive/2-j+tcount+(secondCellExponent Z d 0)-(secondCellExponent Z d 1)+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^0)) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,henergy⟩:=
    actual_priority_cell_recursive (ι:=ι) (σ:=σ) om Φ lo hi hlo hsupport negative B₀ hB₀ 0 J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hz:0<Z:=zero_lt_one.trans hZ
  have hk:∀x∈source,x.second.frequency≠0:=fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)
  rw [physical_source_partition p hp hcop hg source pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ w]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  have hin : cell p source d⊆source:=cell_subset p source d
  have hcommon:∀x∈cell p source d,primeProductNorm p x.second.sourceCommon≤Z^(secondCellExponent Z d 0+eta):=by
    intro x hx
    have hr:primeProductNorm p x.second.sourceCommon≤2*scales d 0:=
      (div_le_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).2.le
    apply hr.trans
    rw [Real.rpow_add hz,second_cell_scale_rpow Z d 0 hZ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbin (show 0≤scales d 0 from (dyadScale_pos _).le)
  have hdiv:∀x∈cell p source d,Z^(secondCellExponent Z d 1-eta)≤primeProductNorm p x.second.divisor:=by
    intro x hx
    have hr:scales d 1≤primeProductNorm p x.second.divisor:=by
      simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 1).1
    have hh:Z^(secondCellExponent Z d 1-eta)≤Z^(secondCellExponent Z d 1):=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    rw [second_cell_scale_rpow Z d 1 hZ] at hh
    exact hh.trans hr
  exact henergy p hp hcop hg hpr hinj hc (cell p source d) (cell_conditions p source hs d) d
    (fun x hx=>(mem_cell p source d x).mp hx |>.2) pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y (R d) L Z X (Vlabel d) εchild ell Ractive j tcount
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta ρ t w (labels d) A
    (fun x hx=>hd₁ x (hin hx)) (fun x hx=>hd₂ x (hin hx)) hρ hL hZ hX hY
    (fun x hx=>by simpa only [(mem_cell p source d x).mp hx |>.2] using hrows x (hin hx)) (fun x hx=>hcube₁ x (hin hx)) (fun x hx=>hcube₂ x (hin hx))
    (fun x hx=>hactive x (hin hx)) (fun x hx=>hj x (hin hx)) (fun x hx=>hquot x (hin hx))
    hcommon hdiv hΨ (fun x hx=>hw x (hin hx)) ha₁ ha₂ (hlabels d hd) ho hslots₁ hslots₂ hA
    (hleft d hd) (hright d hd)

end SevenEighths.InverseMoment

end

end OAI

end Source2509

/- Original source: OAI/NumberTheory/DirichletL/Descent/PriorityCellBudget.lean; sha256: adff0cbb710439fa1b0ebb90fd0e85c28664bcaf0f3a20f16ab680c56477adcd -/
section Source2510
namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment
open InverseSecondSourceBlocks

theorem priority_cell_physical_budget
    (Z:ℝ) (hZ:1<Z) (d:BlockIndex)
    (M r ell V delta A B R j t eta tau pi eps epsmass b C:ℝ)
    (ray:ℂ) (hC:0≤C) (hb:1≤b)
    (hsource:scales d 0*scales d 2≤b*Z^(r-A-B-t))
    (hthreshold:b≤Z^(6*eta))
    (hmass:epsmass*(secondCount ell R j t (secondCellExponent Z d 0)
      (secondCellExponent Z d 1)+11*eta/2)≤pi) :
    let N:=secondCellColumnExponent Z (Z^(r-A-B-t)) d
    let Vchild:=secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta
    C*Z^(firstKappa M r ell V delta A B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (Real.exp (6*(eta*Real.log Z))*
        ‖((Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau):ℝ):ℂ)*ray*
          ((scales d 1*scales d 2*Z^N:ℝ):ℂ)⁻¹‖)*
      Z^((secondCount ell R j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)*(1+epsmass))*
      Z^(2*(max 0 N+Vchild)+eps)≤
    C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps) := by
  intro N Vchild
  have hz:0<Z:=zero_lt_one.trans hZ
  have hclip:=second_cell_clipping_width Z (Z^(r-A-B-t)) b eta d hZ
    (Real.rpow_pos_of_pos hz _) hb hsource hthreshold
  rw [second_cell_formal_column Z r A B t d hZ] at hclip
  have he:=physical_block_scalar_budget Z hZ.le M r ell V delta A B R j t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) (secondCellExponent Z d 2)
    eta tau pi (eps+8*eta) epsmass ray C hC hclip hmass
  dsimp only [N,Vchild]
  rw [second_cell_formal_column Z r A B t d hZ]
  rw [second_cell_scale_rpow Z d 1 hZ,second_cell_scale_rpow Z d 2 hZ] at he
  convert he using 1 <;> congr 1 <;> ring_nf

end SevenEighths.InverseMoment

end

end OAI

end Source2510

/- Original source: OAI/NumberTheory/DirichletL/Descent/PrioritySourceBudget.lean; sha256: 4ff2fa04ab7d73b45324655812923388118c0ccc706c4bbaab5a5c4da9e50ad9 -/
section Source2511
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
local notation "O"=>ActualEisensteinCubic.O

def priorityCellScalar (Z Y L X ell Ractive j t eta eps epsmass B:ℝ) (ray:ℂ) (d:BlockIndex):ℝ :=
  (Real.exp (6*L)*‖(Y:ℂ)*ray*((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
    Z^((secondCount ell Ractive j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)*(1+epsmass))*
    Z^(2*(max 0 (secondCellColumnExponent Z X d)+
      (secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta))+eps)

theorem source_cell_joint_bound {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn)) (hk:∀x∈source,x.second.frequency≠0)
    (b X:ℝ) (hgeom:∀x∈source,primeProductNorm p x.second.sourceCommon*
      primeProductNorm p x.second.overlap≤b*X) (d:BlockIndex) (hd:d∈keys p source):
    scales d 0*scales d 2≤b*X := by
  obtain ⟨x,hx⟩:=(mem_keys_iff p source d).mp hd
  have h0:scales d 0≤primeProductNorm p x.second.sourceCommon:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).1
  have h2:scales d 2≤primeProductNorm p x.second.overlap:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 2).1
  exact (mul_le_mul h0 h2 (dyadScale_pos _).le (primeProductNorm_pos p hp _).le).trans
    (hgeom x (cell_subset p source d hx))

theorem priority_source_scalar_budget (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) :
    ∃ Cbin:ℝ,0≤Cbin ∧ ∀ {ι:Type*} [DecidableEq ι]
    (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B Ractive j t eta tau pi eps epsmass b C:ℝ)
    (ray:ℂ), 2≤Z → 0≤C → 1≤b → b≤Z^(6*eta) →
    (∀x∈source,x.second.frequency≠0) →
    (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
    (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*Z^(r-A-B-t)) →
    (∀d∈keys p source,epsmass*(secondCount ell Ractive j t (secondCellExponent Z d 0)
      (secondCellExponent Z d 1)+11*eta/2)≤pi) →
    C*Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (∑d∈keys p source,priorityCellScalar Z (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
        (eta*Real.log Z) (Z^(r-A-B-t)) ell Ractive j t eta eps epsmass B ray d) ≤
    C*‖ray‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+eps) := by
  refine ⟨capConstant caps,capConstant_nonneg caps hcaps,?_⟩
  intro ι _ p hp _ Jo Jn source Z M r ell V delta A B Ractive j t eta tau pi eps epsmass b C
    ray hZ hC hb hthreshold hk hnorm hgeom hmass
  have hZ':1<Z:=lt_of_lt_of_le (by norm_num) hZ
  have hz:0<Z:=zero_lt_one.trans hZ'
  have hcard:((keys p source).card:ℝ)≤(1+capConstant caps*Real.log Z)^4:=by
    have h:=keys_card_le_product p hp source hk caps Z hnorm
    have hr:((keys p source).card:ℝ)≤∏i:Fin 4,((dyadIndex (Z^(caps i)):ℝ)+1):=by exact_mod_cast h
    apply hr.trans
    calc
      _≤∏_i:Fin 4,(1+capConstant caps*Real.log Z):=
        Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun i _=>cap_bin_bound caps hcaps Z hZ i)
      _= _:=by simp
  rw [Finset.mul_sum]
  calc
    _≤∑_d∈keys p source,C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps):=by
      apply Finset.sum_le_sum
      intro d hd
      have he:=priority_cell_physical_budget Z hZ' d M r ell V delta A B Ractive j t eta tau pi eps epsmass b C
        ray hC hb (source_cell_joint_bound p hp source hk b _ hgeom d hd) hthreshold (hmass d hd)
      convert he using 1 ; dsimp only [priorityCellScalar] ; ring
    _= ((keys p source).card:ℝ)*(C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps)):=by simp
    _≤ (1+capConstant caps*Real.log Z)^4*(C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps)):=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _= _:=by ring

end SevenEighths.InverseMoment

end

end OAI

end Source2511

/- Original source: OAI/NumberTheory/DirichletL/Descent/PriorityRetainedMovingRadius.lean; sha256: ac27c0601724572013c4b2c29e180702f3f30e4c2dcecb042ab312e0ffb25707 -/
section Source2512
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_retained_moving_radius
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,henergy⟩:=
    actual_priority_source_moving_radius (ι:=ι) (σ:=σ) om Φ lo hi hlo hsupport negative B₀ hB₀ J K εmass hεmass
  obtain ⟨Cbin,hCbin,hbudget⟩:=priority_source_scalar_budget caps hcaps
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,36*(2:ℝ)^(2*K)*C,Cbin,by positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b
    ρ t w labels A hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have he:=henergy p hp hcop hg hpr hinj hc source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  let H:ℝ:=(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)
  have hheight:(1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
      (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J=H:=by
    cases negative <;> simp [priorityHeight,H,two_mul,pow_add]
  let D:ℝ:=36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*C*H
  have hD:0≤D:=by dsimp [D,H];positivity
  let S:ℝ:=∑d∈keys p source,priorityCellScalar Z Y L X ell Ractive j tcount eta εchild εmass Bfirst (secondRayCoefficient z) d
  have hfactor:
      (∑d∈keys p source,(Real.exp (6*L)*‖(Y:ℂ)*secondRayCoefficient z*
          ((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel d)+εchild))*
          Z^((ell+Ractive/2-j+tcount+secondCellExponent Z d 0-secondCellExponent Z d 1+11*eta/2)*(1+εmass)))*
          (C*((1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
            (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J))))=D*S:=by
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hheight,hVe d]
    dsimp only [D,priorityCellScalar,secondCount]
    ring
  simp only [pow_zero,div_one] at he
  rw [hfactor] at he
  have hbnd:=hbudget p hp source Z M r ell V delta Acol Bfirst Ractive j tcount eta tau pi εchild εmass b D
    (secondRayCoefficient z) hZ2 hD hb hthreshold
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)) hnorm
    (by simpa only [hXe] using hgeom) hmass
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hP:0≤P:=by dsimp [P];positivity
  have hconst:D≤(36*(2:ℝ)^(2*K)*C)*A*H:=by
    have h1:(2:ℝ)^slots₁.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₁
    have h2:(2:ℝ)^slots₂.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₂
    calc
      _≤36*(2:ℝ)^K*(2:ℝ)^K*A*C*H:=by dsimp only [D];gcongr
      _= _:=by rw [show 2*K=K+K by omega,pow_add];ring
  calc
    _≤P*(D*S):=mul_le_mul_of_nonneg_left he hP
    _≤D*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by
      convert hbnd using 1 ; dsimp only [P,S] ; rw [hYe,hXe,hLe] ; ring
    _≤((36*(2:ℝ)^(2*K)*C)*A*H)*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by gcongr
    _= _:=by dsimp only [H];ring

end SevenEighths.InverseMoment

end

end OAI

end Source2512

/- Original source: OAI/NumberTheory/DirichletL/Inversion/WholePriorityValidSource.lean; sha256: e8350ab7ac886eb026f2e7894e04d9a2bf6008fbd4d985d4080e74a13295fc8e -/
section Source2513
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityValidSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents InversePrioritySecondSource
open InverseMomentWholePriorityParents InverseMomentWholePriorityPhysical
open RayFourExpansion InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ}

def activeFixedSource (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ) :
    Finset (Source ι Jo) :=
  (fixedSource pool b C E old).filter (fun x=>selector x.quotientSupport≠0)

omit [DecidableEq ι] in
theorem activeFixedSource_eq_image (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ) :
    activeFixedSource pool b C E old selector=
      (pool.powerset.filter (fun D=>selector D≠0)).image (fixedPoint b C E old) := by
  rw [activeFixedSource,fixedSource,Finset.filter_image]
  rfl

omit [DecidableEq ι] in
theorem mem_activeFixedSource (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ) (x : Source ι Jo) :
    x∈activeFixedSource pool b C E old selector ↔
      ∃ D∈pool.powerset,selector D≠0 ∧ fixedPoint b C E old D=x := by
  rw [activeFixedSource_eq_image]
  simp only [Finset.mem_image,Finset.mem_filter]
  aesop

omit [DecidableEq ι] in
theorem sum_activeFixedSource {A : Type*} [AddCommMonoid A]
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ) (H : Source ι Jo→A) :
    ∑ x∈activeFixedSource pool b C E old selector,H x=
      ∑ D∈pool.powerset.filter (fun D=>selector D≠0),H (fixedPoint b C E old D) := by
  rw [activeFixedSource_eq_image,Finset.sum_image (fun _ _ _ _ h=>fixedPoint_injective b C E old h)]

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem activeFixedSource_valid (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ)
    (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,selector D≠0 → ∀ i,(old i).val∣
      sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D) :
    ∀ x∈activeFixedSource pool b C E old selector,SourceValid p x := by
  intro x hx
  obtain ⟨D,hD,hs,rfl⟩ := (mem_activeFixedSource pool b C E old selector x).mp hx
  exact ⟨hb,hC,hE,hold D hD hs⟩

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem activeFixedSource_extra (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ)
    (extra : CubeCoordinates ι→Finset ι) (he : extra b⊆b.support) :
    ∀ x∈activeFixedSource pool b C E old selector,extra x.cube⊆x.cube.support := by
  intro x hx
  obtain ⟨D,hD,hs,rfl⟩ := (mem_activeFixedSource pool b C E old selector x).mp hx
  exact he

theorem active_retained_conditions (hp : ∀ i,p i≠0)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ)
    (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,selector D≠0 → ∀ i,(old i).val∣
      sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D)
    (extra : CubeCoordinates ι→Finset ι) (he : extra b⊆b.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p
      (retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube)
        (activeFixedSource pool b C E old selector) negative J lists) R label residual j) :=
  InverseMomentWholeRetainedSource.retained_conditions p hp extra _
    (activeFixedSource_valid p pool b C E old selector hb hC hE hold)
    (activeFixedSource_extra pool b C E old selector extra he) negative J lists pool R label residual j

theorem active_retained_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ)
    (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,selector D≠0 → ∀ i,(old i).val∣
      sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D)
    (extra : CubeCoordinates ι→Finset ι) (he : extra b⊆b.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube)
      (activeFixedSource pool b C E old selector) negative J lists) R label residual j) :
    ∀ i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient :=
  InverseMomentWholeRetainedSource.retained_deleted_support p hinj extra _
    (activeFixedSource_valid p pool b C E old selector hb hC hE hold)
    (activeFixedSource_extra pool b C E old selector extra he) negative J lists pool R label residual j x hx

variable (hp : ∀ i,p i≠0) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem priorityOuter_zero (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (D : Finset ι) (hD : selector D=0) : priorityOuter p hg b negative Ψ m selector r core D=0 := by
  simp only [priorityOuter,hD,norm_zero,mul_zero,zero_mul]

def wholePriorityPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C E extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) (D : Finset ι) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj pool D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (fun U=>primeMark (slots\J)
      (fun i=>lists i\((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)) a U)
    om X (∏ i∈C,p i) (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) core t Y

theorem parentPoisson_fixed_whole (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C E extra D : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) :
    parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra) a om X t Y r core
      (parent p (fixedPoint b C E old D)) =
    wholePriorityPoisson p hp hg hinj pool b C E extra negative Ψ m slots J lists a om X t Y r core D := by
  have hl : residualLists p negative (fun i=>lists i\extra)
      (parent p (fixedPoint b C E old D)) =
      (fun i=>lists i\((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)) := by
    funext i
    unfold residualLists
    rw [quotientSupport_parent p hinj]
    change (lists i\extra)\(((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)=_
    ext k
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  unfold parentPoisson wholePriorityPoisson
  rw [quotientSupport_parent p hinj,hl]
  rfl

variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))

theorem whole_priority_complex_slice [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (extra : CubeCoordinates ι→Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (selector : Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    (∑ D∈pool.powerset,(priorityOuter p hg b negative Ψ m selector r core D:ℂ)*
      (‖primeMark J lists a ((extra b∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)‖^2:ℝ)*
      wholePriorityPoisson p hp hg hinj pool b C E (extra b) negative Ψ m slots J lists a om X t Y r core D) =
    ∑ y∈wholeAssignedParents p (fun x=>extra x.cube) (activeFixedSource pool b C E old selector) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
          (principalWindow om lo hi hlo hs negative t) X Y r core R label y := by
  let H (D : Finset ι) : ℂ := (priorityOuter p hg b negative Ψ m selector r core D:ℂ)*
    (‖primeMark J lists a ((extra b∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)‖^2:ℝ)*
    wholePriorityPoisson p hp hg hinj pool b C E (extra b) negative Ψ m slots J lists a om X t Y r core D
  have hfilter : ∑ D∈pool.powerset,H D=∑ D∈pool.powerset.filter (fun D=>selector D≠0),H D := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro D hD
    by_cases hn : selector D≠0
    · rw [ite_eq_left hn]
    · have hz : selector D=0 := not_ne_iff.mp hn
      simp only [ite_eq_right hn,H,priorityOuter_zero p hg b negative Ψ m selector r core D hz,
        Complex.ofReal_zero,zero_mul]
  calc
    _ = ∑ D∈pool.powerset.filter (fun D=>selector D≠0),H D := hfilter
    _ = ∑ x∈activeFixedSource pool b C E old selector,
        (priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)*
        (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube) a om X t Y r core (parent p x) := by
      rw [sum_activeFixedSource]
      apply Finset.sum_congr rfl
      intro D hD
      rw [parentPoisson_fixed_whole p hp hg hinj]
      simp only [H,fixedPoint,wholeExtractedSupport,extractedSupport,Finset.union_assoc]
    _ = _ := whole_signed_source_full p hp hcop hg hinj hc hpr extra pool _ _ negative Ψ m slots J lists a
      om lo hi hlo hs X t Y hX hY r core R label

theorem whole_priority_real_slice [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (extra : CubeCoordinates ι→Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (selector : Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    (∑ D∈pool.powerset,priorityOuter p hg b negative Ψ m selector r core D*
      ‖primeMark J lists a ((extra b∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)‖^2*
      (wholePriorityPoisson p hp hg hinj pool b C E (extra b) negative Ψ m slots J lists a om X t Y r core D).re) =
    (∑ y∈wholeAssignedParents p (fun x=>extra x.cube) (activeFixedSource pool b C E old selector) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
          (principalWindow om lo hi hlo hs negative t) X Y r core R label y).re := by
  have h := congrArg Complex.re (whole_priority_complex_slice p hp hg hcop hinj hc hpr pool b C E
    extra old negative Ψ m slots J lists a selector om lo hi hlo hs X t Y hX hY r core R label)
  simpa only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero] using h

theorem whole_priority_energy_reassembly [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (extra : CubeCoordinates ι→Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (selector : Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    firstWholePrioritySecondEnergy p hp hg hinj pool b C (extra b) negative Ψ m
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) slots lists a selector om X t Y =
    (32*512)*(2:ℝ)^slots.card * ∑ r : RayCharacter×RayCharacter,
      ∑ core : FirstCoreIndex,∑ J∈slots.powerset,
        (∑ y∈wholeAssignedParents p (fun x=>extra x.cube) (activeFixedSource pool b C E old selector) negative J lists,
          coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
            fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
              (principalWindow om lo hi hlo hs negative t) X Y r core R label y).re := by
  simp_rw [←whole_priority_real_slice p hp hg hcop hinj hc hpr pool b C E extra old negative Ψ m slots
    _ lists a selector om lo hi hlo hs X t Y hX hY _ _ R label]
  unfold firstWholePrioritySecondEnergy
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro core hcore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro D hD
  unfold priorityOuter wholePriorityPoisson
  ring

end SevenEighths.InverseWholePriorityValidSource

end

end OAI

end Source2513

/- Original source: OAI/NumberTheory/DirichletL/Inversion/WholePriorityRetainedSource.lean; sha256: 1cb49f206a6689ef6ca49237d274381a6c687a944ea6638e11ec21e037c17e5b -/
section Source2514
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityRetainedSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents InversePrioritySecondSource
open InverseMomentWholePriorityParents InverseMomentWholePriorityPhysical
open InverseWholePriorityValidSource RayFourExpansion InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def unifiedSource (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ) :
    Finset (MarkedSecondSource ι Jo 0) :=
  attachedSecondFamily parents (fun y=>secondExpansionPool pool
    (fun G E=>(secondVariableCutoff p y (R y) G E).erase 0))

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem mem_unifiedSource (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ) (x : MarkedSecondSource ι Jo 0) :
    x∈unifiedSource p pool parents R ↔ secondParentOf x∈parents ∧
      x.second.sourceCommon⊆pool ∧ x.second.divisor⊆x.second.sourceCommon ∧
      x.second.overlap⊆pool ∧ x.second.frequency∈nonzeroChildFrequencyBall
        (actualSecondMultiplier p x) (R (secondParentOf x) x.second.sourceCommon x.second.divisor) := by
  rw [unifiedSource,mem_attachedSecondFamily,mem_secondExpansionPool]
  rfl

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem unified_frequency_ne_zero (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈unifiedSource p pool parents R) : x.second.frequency≠0 :=
  (Finset.mem_erase.mp ((mem_unifiedSource p pool parents R x).mp hx).2.2.2.2).1

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem unified_mem_sector
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (x : MarkedSecondSource ι Jo 0) (hx : x∈unifiedSource p pool parents R) :
    x∈retainedPool p pool parents R label (x.second.sourceCommon\x.second.divisor)
      (label (secondParentOf x) (x.second.sourceCommon\x.second.divisor) x.second) := by
  obtain ⟨hy,hz⟩ := (mem_attachedSecondFamily _ _ x).mp hx
  apply (mem_retainedPool p _ _ _ _ _ _ x).mpr
  exact ⟨hy,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hz,rfl⟩,rfl⟩⟩

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem sectors_sum [Fintype κ]
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (H : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ residual∈pool.powerset,∑ j : κ,∑ x∈retainedPool p pool parents R label residual j,H x)=
      ∑ x∈unifiedSource p pool parents R,H x := by
  simp only [retainedPool,unifiedSource,sum_attachedSecondFamily]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_comm]
  simp_rw [sum_secondDyadicSector]
  exact sum_secondExpansionSector pool _ _

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem parent_retained_sum [Fintype κ]
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (w : SecondParentSource ι Jo→ℂ) (H : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ y∈parents,w y*(∑ residual∈pool.powerset,∑ j : κ,
      ∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
        (attachSecondExpansion y),H x)) =
      ∑ x∈unifiedSource p pool parents R,w (secondParentOf x)*H x := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext residual; rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum,retained_sum]
  exact sectors_sum p pool parents R label _

theorem unified_conditions (hp : ∀ i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (source : Finset (Source ι Jo))
    (hs : ∀ x∈source,SourceValid p x) (he : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ) :
    ActualSecondSourceConditions p (unifiedSource p pool
      (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists) R) := by
  apply whole_assigned_family_conditions p hp (fun x=>extra x.cube) source hs he negative J lists
  intro y hy x hx
  exact ((mem_secondExpansionPool _ _ x).mp hx).2.1

theorem unified_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (source : Finset (Source ι Jo))
    (hs : ∀ x∈source,SourceValid p x) (he : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube)
      source negative J lists) R) :
    ∀ i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient := by
  exact InverseMomentWholeRetainedSource.retained_deleted_support p hinj extra source hs he
    negative J lists pool R (fun _ _ _=>()) _ () x
    (unified_mem_sector p pool _ R (fun _ _ _=>()) x hx)

omit [DecidableEq σ] [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem deleted_lists (extra : CubeCoordinates ι→Finset ι) (negative : Bool)
    (lists : σ→Finset ι) (x : MarkedSecondSource ι Jo 0) :
    residualLists p negative (fun i=>lists i\extra x.cube) (secondParentOf x)=
      fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x := by
  funext i
  ext k
  simp only [residualLists,InverseMomentWholeRetainedSource.deleted,Finset.mem_sdiff,Finset.mem_union]
  tauto

def wholeRow (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0) : ℂ :=
  retainedRow p hp hcop hg pool negative Ψ m slots J (fun i=>lists i\extra x.cube) a V X Y ray x

theorem wholeRow_eq (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0) :
    wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a V X Y ray x =
      actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
        (slots\J) (slots\J)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        a a V V rowMajorant Y X := by
  unfold wholeRow retainedRow
  rw [deleted_lists]

theorem whole_retained_sum [Fintype κ] (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (parents : Finset (SecondParentSource ι Jo)) (w : SecondParentSource ι Jo→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (V : ℝ→ℂ) (X Y : ℝ)
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ) :
    (∑ y∈parents,w y*(∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
          (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ m slots J (fun i=>lists i\extra y.cube)
            a V X Y ray x)) =
    ∑ ray : SecondRayIndex,(Y:ℂ)*secondRayCoefficient ray *
      ∑ x∈unifiedSource p pool parents R,w (secondParentOf x)*
        wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a V X Y ray x := by
  have hrow (y : SecondParentSource ι Jo) (ray : SecondRayIndex) (residual : Finset ι) (j : κ) :
      (∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
          (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ m slots J (fun i=>lists i\extra y.cube)
            a V X Y ray x) =
      ∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
          (attachSecondExpansion y),
          wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a V X Y ray x := by
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    rfl
  simp_rw [hrow,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray hray
  simp_rw [←Finset.mul_sum]
  simp_rw [mul_left_comm _ ((Y:ℂ)*secondRayCoefficient ray),←Finset.mul_sum]
  congr 1
  exact parent_retained_sum p pool parents R label w _

def activeParents (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (b : CubeCoordinates ι) (C E : Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector : Finset ι→ℂ) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) :=
  wholeAssignedParents p (fun x=>extra x.cube)
    (activeFixedSource pool b C E old selector) negative J lists

theorem active_conditions (hp : ∀ i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (b : CubeCoordinates ι) (C E : Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector : Finset ι→ℂ) (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,selector D≠0 → ∀ i,(old i).val∣
      sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D)
    (he : extra b⊆b.support) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ) :
    ActualSecondSourceConditions p (unifiedSource p pool
      (activeParents p extra pool b C E old selector negative J lists) R) :=
  unified_conditions p hp extra _ (activeFixedSource_valid p pool b C E old selector hb hC hE hold)
    (activeFixedSource_extra pool b C E old selector extra he) negative J lists pool R

theorem active_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (b : CubeCoordinates ι) (C E : Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector : Finset ι→ℂ) (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,selector D≠0 → ∀ i,(old i).val∣
      sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D)
    (he : extra b⊆b.support) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈unifiedSource p pool (activeParents p extra pool b C E old selector negative J lists) R) :
    ∀ i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient :=
  unified_deleted_support p hinj extra _
    (activeFixedSource_valid p pool b C E old selector hb hC hE hold)
    (activeFixedSource_extra pool b C E old selector extra he) negative J lists pool R x hx

def coefficientBound : ℝ := 512*(32*512)

theorem coefficientBound_pos : 0<coefficientBound := by norm_num [coefficientBound]

variable (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem priorityOuter_norm (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) (D : Finset ι)
    (hselector : ‖selector D‖≤1) (hΨ : ‖Ψ (∏ i∈D,p i)‖≤1) :
    ‖(priorityOuter p hg b negative Ψ m selector r core D:ℂ)‖≤coefficientBound := by
  have hr : ‖crossCoeff r.1 r.2‖≤512 :=
    (Finset.single_le_sum (fun j _=>norm_nonneg (crossCoeff r.1 j)) (Finset.mem_univ r.2)).trans
      ((Finset.single_le_sum (fun j _=>Finset.sum_nonneg (fun k _=>norm_nonneg (crossCoeff j k)))
        (Finset.mem_univ r.1)).trans crossCoeff_sum_norm_le)
  have hc : ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit negative Ψ m D core‖≤32*512 :=
    (Finset.single_le_sum (fun c _=>norm_nonneg (firstCoreOuter p hg b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D c))
      (Finset.mem_univ core)).trans
      (firstCoreOuter_mass p hg b.support _ b.leftBit b.rightBit negative Ψ m D hΨ)
  rw [Complex.norm_real,Real.norm_of_nonneg (by unfold priorityOuter; positivity)]
  unfold priorityOuter coefficientBound
  exact mul_le_mul ((mul_le_of_le_one_right (norm_nonneg _) hselector).trans hr) hc
    (norm_nonneg _) (by norm_num)

def sourceWeight (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (J : Finset σ) (a : σ→ι→ℂ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0) : ℂ :=
  coefficient p J a (fun original=>(priorityOuter p hg b negative Ψ m selector r core
    original.quotientSupport:ℂ)) (secondParentOf x)

theorem sourceWeight_norm
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (b : CubeCoordinates ι) (C E : Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector : Finset ι→ℂ) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1)
    (hselector : ∀ D∈pool.powerset,‖selector D‖≤1)
    (hΨ : ∀ D∈pool.powerset,selector D≠0 → ‖Ψ (∏ i∈D,p i)‖≤1)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈unifiedSource p pool (activeParents p extra pool b C E old selector negative J lists) R) :
    ‖sourceWeight p hg b negative Ψ m selector r core J a x‖≤coefficientBound := by
  apply InverseMomentWholeRetainedSource.whole_coefficient_norm p hinj (fun x=>extra x.cube)
    (activeFixedSource pool b C E old selector) negative J lists a _ coefficientBound ha
  · intro y hy
    obtain ⟨D,hD,hs,rfl⟩ := (mem_activeFixedSource pool b C E old selector y).mp hy
    exact priorityOuter_norm p hg b negative Ψ m selector r core D (hselector D hD) (hΨ D hD hs)
  · exact ((mem_unifiedSource p pool _ R x).mp hx).1

def normalizedWeight (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (J : Finset σ) (a : σ→ι→ℂ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0) : ℂ :=
  sourceWeight p hg b negative Ψ m selector r core J a x/(coefficientBound:ℂ)

theorem normalizedWeight_norm
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (b : CubeCoordinates ι) (C E : Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector : Finset ι→ℂ) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1)
    (hselector : ∀ D∈pool.powerset,‖selector D‖≤1)
    (hΨ : ∀ D∈pool.powerset,selector D≠0 → ‖Ψ (∏ i∈D,p i)‖≤1)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈unifiedSource p pool (activeParents p extra pool b C E old selector negative J lists) R) :
    ‖normalizedWeight p hg b negative Ψ m selector r core J a x‖≤1 := by
  rw [normalizedWeight,norm_div,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  exact (div_le_one coefficientBound_pos).mpr
    (sourceWeight_norm p hg hinj extra pool b C E old selector negative Ψ m r core J lists a
      ha hselector hΨ R x hx)

omit [DecidableEq σ] in

theorem source_sum_normalized
    (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (J : Finset σ) (a : σ→ι→ℂ) (source : Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0))
    (H : MarkedSecondSource ι (Jo+(J.card+J.card)) 0→ℂ) :
    (∑ x∈source,sourceWeight p hg b negative Ψ m selector r core J a x*H x)=
      (coefficientBound:ℂ)*∑ x∈source,normalizedWeight p hg b negative Ψ m selector r core J a x*H x := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  unfold normalizedWeight
  have hc : (coefficientBound:ℂ)≠0 := by exact_mod_cast coefficientBound_pos.ne'
  field_simp

theorem fullPhysical_unified [Fintype κ] (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (parents : Finset (SecondParentSource ι Jo)) (w : SecondParentSource ι Jo→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (V : 𝓢(ℝ,ℂ)) (X Y : ℝ)
    (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    let H := fun y : SecondParentSource ι Jo=>markedRadial p (slots\J)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X
    let K := fun y : SecondParentSource ι Jo=>secondVariableCutoff p y R
    (∑ y∈parents,w y*fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
      V X Y r core R label y) =
      (∑ y∈parents,w y*truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) +
      (∑ ray : SecondRayIndex,(Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈unifiedSource p pool parents (fun _=>R),w (secondParentOf x)*
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots J lists a V X Y ray x) +
      (∑ y∈parents,w y*secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) := by
  intro Ψ₀ H K
  simp only [fullPhysical,mul_add,Finset.sum_add_distrib]
  rw [whole_retained_sum p hp hcop hg extra pool parents w negative Ψ₀ m slots J lists a
    V X Y (fun _=>R) (fun _=>label)]

theorem actual_retained_normalized [Fintype κ] (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (b : CubeCoordinates ι) (C E : Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector : Finset ι→ℂ) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ) :
    let parents := activeParents p extra pool b C E old selector negative J lists
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    (∑ y∈parents,
      coefficient p J a (fun original=>(priorityOuter p hg b negative Ψ m selector r core
        original.quotientSupport:ℂ)) y *
      (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
        (Y:ℂ)*secondRayCoefficient ray *
          ∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
            (attachSecondExpansion y),
            retainedRow p hp hcop hg pool negative Ψ₀ m slots J (fun i=>lists i\extra y.cube)
              a V X Y ray x)) =
    (coefficientBound:ℂ)*(∑ ray : SecondRayIndex,(Y:ℂ)*secondRayCoefficient ray *
      ∑ x∈unifiedSource p pool parents R,normalizedWeight p hg b negative Ψ m selector r core J a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots J lists a V X Y ray x) := by
  intro parents Ψ₀
  rw [whole_retained_sum p hp hcop hg extra pool parents _ negative Ψ₀ m slots J lists a V X Y R label]
  change (∑ ray : SecondRayIndex,(Y:ℂ)*secondRayCoefficient ray *
      ∑ x∈unifiedSource p pool parents R,sourceWeight p hg b negative Ψ m selector r core J a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots J lists a V X Y ray x)=_
  simp_rw [source_sum_normalized]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ray hray
  ring

end SevenEighths.InverseWholePriorityRetainedSource

end

end OAI

end Source2514

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPrioritySource.lean; sha256: 394b3a3d5d4d6a25e3f2bf7ccf65dbbf2167fad3d8b49fe3b1d12baf0f9aedbf -/
section Source2515
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def globalPriorityOuter (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)(x:Source ι Jo):ℂ:=
  w x*(priorityOuter p hg x.cube negative Ψ m (fun _=>1) ray core x.quotientSupport:ℂ)

def globalPriorityWeight (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)
    (J:Finset σ)(a:σ→ι→ℂ)(x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0):ℂ:=
  coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) (secondParentOf x)

def normalizedGlobalPriorityWeight (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)
    (J:Finset σ)(a:σ→ι→ℂ)(x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0):ℂ:=
  globalPriorityWeight p hg negative Ψ m ray core w J a x/(coefficientBound:ℂ)

theorem globalPriorityWeight_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(original:Finset (Source ι Jo))(pool:Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(hw:∀x∈original,‖w x‖≤1)(hΨ:∀u,‖Ψ u‖≤1)
    (J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ha:∀i∈J,∀k∈lists i,‖a i k‖≤1)
    (R:SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx:x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) R):
    ‖globalPriorityWeight p hg negative Ψ m ray core w J a x‖≤coefficientBound:=by
  apply InverseMomentWholeRetainedSource.whole_coefficient_norm p hinj (fun x=>extra x.cube)
    original negative J lists a _ coefficientBound ha
  · intro y hy
    rw [globalPriorityOuter,norm_mul]
    have hn:=priorityOuter_norm p hg y.cube negative Ψ m (fun _=>1) ray core y.quotientSupport
      (by simp) (hΨ _)
    exact (mul_le_mul (hw y hy) hn (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · exact ((mem_unifiedSource p pool _ R x).mp hx).1

theorem normalizedGlobalPriorityWeight_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(original:Finset (Source ι Jo))(pool:Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(hw:∀x∈original,‖w x‖≤1)(hΨ:∀u,‖Ψ u‖≤1)
    (J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ha:∀i∈J,∀k∈lists i,‖a i k‖≤1)
    (R:SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx:x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) R):
    ‖normalizedGlobalPriorityWeight p hg negative Ψ m ray core w J a x‖≤1:=by
  rw [normalizedGlobalPriorityWeight,norm_div,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  exact (div_le_one coefficientBound_pos).mpr
    (globalPriorityWeight_norm p hg hinj extra original pool negative Ψ m ray core w hw hΨ J lists a ha R x hx)

omit [DecidableEq σ] in
theorem globalPriority_sum_normalized
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(J:Finset σ)(a:σ→ι→ℂ)
    (source:Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0))
    (H:MarkedSecondSource ι (Jo+(J.card+J.card)) 0→ℂ):
    (∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w J a x*H x)=
      (coefficientBound:ℂ)*∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w J a x*H x:=by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  unfold normalizedGlobalPriorityWeight
  have hn:(coefficientBound:ℂ)≠0:=by exact_mod_cast coefficientBound_pos.ne'
  field_simp
end SevenEighths.InverseMoment

end

end OAI

end Source2515

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityEnergy.lean; sha256: 859e3848934076d3000247134e8f9cc5bdd03055f3e3d6ef64afc521205f15a7 -/
section Source2516
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_retained_moving_radius
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
,
    let source:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀(z:SecondRayIndex)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y:ℂ)*secondRayCoefficient z *
        ∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,Cbin,hC,hCbin,he⟩:=
    actual_priority_retained_moving_radius (ι:=ι) (σ:=σ) om rowMajorant lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,coefficientBound*C,Cbin,mul_nonneg coefficientBound_pos.le hC,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff source Ψ₀ z
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hsource:ActualSecondSourceConditions p source:=
    unified_conditions p hp extra original hvalid hextra negative assigned lists pool cutoff
  have hd:∀x∈source,∀i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient:=
    unified_deleted_support p hinj extra original hvalid hextra negative assigned lists pool cutoff
  have hw:∀x∈source,‖normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x‖≤1:=
    fun x hx=>normalizedGlobalPriorityWeight_norm p hg hinj extra original pool negative Ψ m ray core w hwOriginal hΨ
      assigned lists a haassigned cutoff x hx
  have hΨ₀:∀n,‖Ψ₀ n‖≤1:=fun n=>(firstCoreTwist_norm_le negative (if negative then ray.1 else ray.2)
    Ψ core n).trans (hΨ n)
  have he₀:=he p hp hcop hg hpr hinj hc source hsource pool Ψ₀ m z (slots\assigned) (slots\assigned)
    lists lists a a (InverseMomentWholeRetainedSource.deleted p extra negative)
    (InverseMomentWholeRetainedSource.deleted p extra negative)
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t
    (normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a) labels A
    hd hd hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ₀ hw
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hrow:∀x:MarkedSecondSource ι (Jo+(assigned.card+assigned.card)) 0,wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
      (principalWindow om lo hi hlo hsupport negative t) X Y z x=
      actualSecondSignedWeight p hp hcop hg Ψ₀ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ₀ m z)
        (slots\assigned) (slots\assigned)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x) a a
        (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t)
        rowMajorant Y X:=fun x=>wholeRow_eq p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a _ X Y z x
  rw [globalPriority_sum_normalized p hg negative Ψ m ray core w assigned a source]
  rw [show (Y:ℂ)*secondRayCoefficient z*((coefficientBound:ℂ)*
      ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x)=
      (coefficientBound:ℂ)*((Y:ℂ)*secondRayCoefficient z*
        ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x) by ring]
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  simp_rw [hrow,←mul_assoc]
  convert mul_le_mul_of_nonneg_left he₀ coefficientBound_pos.le using 1 <;> ring_nf

end SevenEighths.InverseMoment

end

end OAI

end Source2516

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityPhysical.lean; sha256: ab115afca7821d08fc058bc74a080397659dff4b576bcd28a9ab2b3d6b3b9096 -/
section Source2517
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_priority_physical_source
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(slots J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ)(hX:0<X)(hY:0<Y)(R:Finset ι→Finset ι→ℝ):
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative J lists
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let V:=principalWindow om lo hi hlo hs negative t
    let H:=fun y:SecondParentSource ι (Jo+(J.card+J.card))=>markedRadial p (slots\J)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X
    let K:=fun y:SecondParentSource ι (Jo+(J.card+J.card))=>secondVariableCutoff p y R
    let coeff:=coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w)
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
        a om X t Y ray core (parent p x))=
    (∑y∈parents,coeff y*truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y))+
    (∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z*
      ∑x∈unifiedSource p pool parents (fun _=>R),globalPriorityWeight p hg negative Ψ m ray core w J a x*
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots J lists a V X Y z x)+
    (∑y∈parents,coeff y*secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)):=by
  intro parents Ψ₀ V H K coeff
  rw [whole_signed_source_full p hp hcop hg hinj hc hpr extra pool original
    (globalPriorityOuter p hg negative Ψ m ray core w) negative Ψ m slots J lists a
    om lo hi hlo hs X t Y hX hY ray core R (fun _ _=>())]
  exact fullPhysical_unified p hg hp hcop hinj extra pool parents coeff negative Ψ m slots J lists a
    V X Y ray core R (fun _ _=>())
end SevenEighths.InverseMoment

end

end OAI

end Source2517

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalParentSource.lean; sha256: 891b92430a3269def4e399f6cf3300a9be7acb5d42c1a1df59e26761114bb8cd -/
section Source2518
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open InverseFirstPriorityParents
variable {ι:Type*} [DecidableEq ι] {Jo:ℕ}
def eraseFirstQuotient (x:Source ι Jo):Source ι Jo:= {x with quotientSupport:=∅}
def fillFirstQuotient (x:Source ι Jo)(D:Finset ι):Source ι Jo:={x with quotientSupport:=D}
omit [DecidableEq ι] in
@[simp] theorem erase_fillFirstQuotient (x:Source ι Jo)(D:Finset ι):
    eraseFirstQuotient (fillFirstQuotient x D)=eraseFirstQuotient x:=rfl
omit [DecidableEq ι] in
@[simp] theorem eraseFirstQuotient_eq (x:Source ι Jo)(hx:x.quotientSupport=∅):
    eraseFirstQuotient x=x:=by cases x;simpa [eraseFirstQuotient] using hx.symm

def globalParentSource (outer:Finset (Source ι Jo))(pool:Finset ι)
    (selector:Source ι Jo→Finset ι→ℂ):Finset (Source ι Jo):=
  outer.biUnion (fun x=>(pool.powerset.filter (fun D=>selector x D≠0)).image (fillFirstQuotient x))

omit [DecidableEq ι] in
theorem sum_globalParentSource {A:Type*}[AddCommMonoid A]
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(H:Source ι Jo→A):
    ∑x∈globalParentSource outer pool selector,H x=
      ∑x∈outer,∑D∈pool.powerset.filter (fun D=>selector x D≠0),H (fillFirstQuotient x D):=by
  unfold globalParentSource
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro x hx
    exact Finset.sum_image (fun D hD E hE he=>congrArg Source.quotientSupport he)
  · intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hz
    obtain ⟨E,hE,he⟩:=Finset.mem_image.mp hz'
    have he':=congrArg eraseFirstQuotient he
    simp only [erase_fillFirstQuotient,eraseFirstQuotient_eq _ (houter x hx),
      eraseFirstQuotient_eq _ (houter y hy)] at he'
    exact hxy he'.symm

omit [DecidableEq ι] in
theorem mem_globalParentSource
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(x:Source ι Jo):
    x∈globalParentSource outer pool selector ↔
      eraseFirstQuotient x∈outer ∧ x.quotientSupport⊆pool ∧
        selector (eraseFirstQuotient x) x.quotientSupport≠0:=by
  constructor
  · intro hx
    obtain ⟨y,hy,hyx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hyx
    simp only [erase_fillFirstQuotient,eraseFirstQuotient_eq _ (houter y hy)]
    exact ⟨hy,Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1,(Finset.mem_filter.mp hD).2⟩
  · rintro ⟨hx,hD,hs⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨eraseFirstQuotient x,hx,Finset.mem_image.mpr ⟨x.quotientSupport,?_,?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hD,hs⟩
    · cases x;rfl
end SevenEighths.InverseMoment

end

end OAI

end Source2518

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalParentEnergy.lean; sha256: 40121df6d7a7ca0b8908b0ff36d8f326f422331951968759f631d06e60a7c786 -/
section Source2519
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityValidSource
open InversePrioritySecondSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_original_priority_slice
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (H:Source ι Jo→ℂ):
    (∑x∈globalParentSource outer pool selector,
      globalPriorityOuter p hg negative Ψ m ray core
        (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ)) x*H x)=
    ∑x∈outer,∑D∈pool.powerset,
      (priorityOuter p hg x.cube negative Ψ m (selector x) ray core D:ℂ)*H (fillFirstQuotient x D):=by
  rw [sum_globalParentSource outer pool selector houter]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector x D≠0
  · rw [ite_eq_left hs]
    simp only [globalPriorityOuter,erase_fillFirstQuotient,eraseFirstQuotient_eq _ (houter x hx)]
    dsimp only [fillFirstQuotient,priorityOuter]
    simp only [norm_one,mul_one,Complex.ofReal_mul]
    ring
  · rw [ite_eq_right hs,priorityOuter_zero p hg x.cube negative Ψ m (selector x) ray core D (not_ne_iff.mp hs)]
    simp

theorem global_second_energy_source
    (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(extra:CubeCoordinates ι→Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ):
    (∑x∈outer,firstWholePrioritySecondEnergy p hp hg hinj pool x.cube x.firstCommon
      (extra x.cube) negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
      slots lists a (selector x) om X t Y)=
    (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
      (∑x∈globalParentSource outer pool selector,
        globalPriorityOuter p hg negative Ψ m ray core
          (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ)) x*
        (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
          a om X t Y ray core (parent p x)).re:=by
  have hs (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(J:Finset σ):
      (∑x∈globalParentSource outer pool selector,
        globalPriorityOuter p hg negative Ψ m ray core
          (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ)) x*
        (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
          a om X t Y ray core (parent p x))=
      ∑x∈outer,∑D∈pool.powerset,(priorityOuter p hg x.cube negative Ψ m (selector x) ray core D:ℂ)*
        (‖primeMark J lists a ((extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪D)‖^2:ℝ)*
        wholePriorityPoisson p hp hg hinj pool x.cube x.firstCommon x.firstDivisor (extra x.cube)
          negative Ψ m slots J lists a om X t Y ray core D:=by
    simp_rw [mul_assoc]
    rw [global_original_priority_slice p hg outer pool selector houter negative Ψ m ray core]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro D hD
    have hm : wholeExtractedSupport (fun x=>extra x.cube) negative (fillFirstQuotient x D)=
        ((extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪D) := by
      simp only [wholeExtractedSupport,extractedSupport,fillFirstQuotient,Finset.union_assoc]
    rw [hm]
    have hf : fillFirstQuotient x D = fixedPoint x.cube x.firstCommon x.firstDivisor x.oldAssigned D := by
      cases x;rfl
    rw [hf]
    change (priorityOuter p hg x.cube negative Ψ m (selector x) ray core D:ℂ)*
      ((‖primeMark J lists a ((extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪D)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
          a om X t Y ray core (parent p (fixedPoint x.cube x.firstCommon x.firstDivisor x.oldAssigned D))) = _
    rw [parentPoisson_fixed_whole p hp hg hinj]
  simp_rw [hs]
  simp only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
  unfold firstWholePrioritySecondEnergy
  simp only [Finset.mul_sum,wholePriorityPoisson,priorityOuter]
  rw [Finset.sum_comm (s:=outer)]
  apply Finset.sum_congr rfl
  intro ray hray
  simp_rw [Finset.sum_comm (s:=pool.powerset) (t:=(Finset.univ : Finset FirstCoreIndex))]
  rw [Finset.sum_comm (s:=outer)]
  apply Finset.sum_congr rfl
  intro core hcore
  simp_rw [Finset.sum_comm (s:=pool.powerset) (t:=slots.powerset)]
  rw [Finset.sum_comm (s:=outer)]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro D hD
  ring
end SevenEighths.InverseMoment

end

end OAI

end Source2519
