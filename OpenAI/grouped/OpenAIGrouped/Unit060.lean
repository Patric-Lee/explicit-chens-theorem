import OpenAIGrouped.Unit059
import OpenAIGrouped.Unit058
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit037
import OpenAIGrouped.Unit040

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondVaryingLists.lean; sha256: d9d50510bd8903ac769021366fe31351147866e0c778420d00bc9c388bf4f4a6 -/
section Source2400
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open InverseSecondFibers
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def varyingAssignedGate {Jo : ℕ} (J₁ J₂ : Finset σ)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) : Prop :=
  (∀ i hi,x.newAssigned (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))∈L₁ (eraseSecondSlots x) i) ∧
  (∀ i hi,x.newAssigned (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))∈L₂ (eraseSecondSlots x) i)

omit [DecidableEq ι] in
lemma varyingAssignedGate_attach {Jo : ℕ} (J₁ J₂ : Finset σ)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (x : MarkedSecondSource ι Jo 0) (q : (∀ i∈J₁,ι)×(∀ i∈J₂,ι)) :
    varyingAssignedGate J₁ J₂ L₁ L₂ (attachPairedSlots J₁ J₂ (x,q)) ↔
      q.1∈J₁.pi (L₁ x) ∧ q.2∈J₂.pi (L₂ x) := by
  simp only [varyingAssignedGate,attachPairedSlots,erase_attachSecondSlots]
  simp only [attachSecondSlots,pairedSlotAssignment,
    Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,Finset.mem_pi]

def varyingAssignedSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι) :=
  (assignedSecondSource source J₁ J₂ base₁ base₂).filter (varyingAssignedGate J₁ J₂ L₁ L₂)

theorem varyingAssignedSource_mono {Jo : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo 0)} (hST : S⊆T)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι) :
    varyingAssignedSource S J₁ J₂ base₁ base₂ L₁ L₂⊆
      varyingAssignedSource T J₁ J₂ base₁ base₂ L₁ L₂ := by
  exact Finset.filter_subset_filter _ (assignedSecondSource_mono hST J₁ J₂ base₁ base₂)

theorem varyingAssignedSource_sum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (F : MarkedSecondSource ι Jo (J₁.card+J₂.card)→ℂ) :
    ∑ x∈varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂,F x =
      ∑ y∈source,∑ q∈(J₁.pi (fun i=>L₁ y i∩(y.second.sourceCommon∪y.second.overlap)))×ˢ
        (J₂.pi (fun i=>L₂ y i∩(y.second.sourceCommon∪y.second.overlap))),F (attachPairedSlots J₁ J₂ (y,q)) := by
  rw [varyingAssignedSource,Finset.sum_filter,assignedSecondSource_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  congr 1
  ext q
  simp only [Finset.mem_filter,Finset.mem_product,varyingAssignedGate_attach,Finset.mem_pi,Finset.mem_inter]
  constructor
  · rintro ⟨⟨h₁,h₂⟩,h₃,h₄⟩
    exact ⟨fun i hi=>⟨h₃ i hi,(h₁ i hi).2⟩,fun i hi=>⟨h₄ i hi,(h₂ i hi).2⟩⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨⟨fun i hi=>⟨hL₁ y hy i hi (h₁ i hi).1,(h₁ i hi).2⟩,
      fun i hi=>⟨hL₂ y hy i hi (h₂ i hi).1,(h₂ i hi).2⟩⟩,
      fun i hi=>(h₁ i hi).1,fun i hi=>(h₂ i hi).1⟩

theorem varyingAssignedSource_sum_marks {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (a₁ a₂ : σ→ι→ℂ) (w P : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ y∈source,w y*(star (primeMark J₁ (L₁ y) a₁ (y.second.sourceCommon∪y.second.overlap))*
      primeMark J₂ (L₂ y) a₂ (y.second.sourceCommon∪y.second.overlap))*P y) =
    ∑ x∈varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂,
      (w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x)*P (eraseSecondSlots x) := by
  rw [varyingAssignedSource_sum source J₁ J₂ base₁ base₂ L₁ L₂ hL₁ hL₂]
  apply Finset.sum_congr rfl
  intro y hy
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [assignedSecondCoefficient_attach]
  simp only [attachPairedSlots,erase_attachSecondSlots]

variable (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem actual_second_varying_lists_weighted_count
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {Jo : ℕ} (u v : Oˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (a₁ a₂ : σ→ι→ℂ)
    (ha₁ : ∀ i∈J₁,∀ q∈base₁ i,‖a₁ i q‖≤1)
    (ha₂ : ∀ i∈J₂,∀ q∈base₂ i,‖a₂ i q‖≤1)
    (labels : Finset (Ideal O)) (rows : Finset O)
    (hchild : ∀ x∈source,(actualSecondChild p u v x).2.1∈labels ∧ (actualSecondChild p u v x).2.2∈rows)
    (K : ℕ) (ho : Jo≤2*K) (hJ₁ : J₁.card≤K) (hJ₂ : J₂.card≤K)
    (w : MarkedSecondSource ι Jo 0→ℂ) (hw : ∀ x∈source,‖w x‖≤1) (F G : SecondChild→ℂ) :
    ‖∑ x∈source,w x*(star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap))*
      primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap))*
      F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x))‖ ≤
    Real.sqrt (∑ γ∈actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
      tripleDivisorWeight K γ*secondLabelEnergy K labels rows F γ)*
    Real.sqrt (∑ γ∈actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
      tripleDivisorWeight K γ*secondLabelEnergy K labels rows G γ) := by
  let S := varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂
  have hsub : S⊆assignedSecondSource source J₁ J₂ base₁ base₂ := Finset.filter_subset _ _
  have hs' : ActualSecondSourceConditions p S :=
    (assignedSecondSource_conditions p source hs J₁ J₂ base₁ base₂).mono p hsub
  have herase : ∀ x∈S,eraseSecondSlots x∈source := by
    intro x hx
    obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ base₁ base₂ x).mp (hsub hx)
    simpa only [attachPairedSlots,erase_attachSecondSlots] using hy
  let w' := fun x : MarkedSecondSource ι Jo (J₁.card+J₂.card)=>
    w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x
  have hw' : ∀ x∈S,‖w' x‖≤1 := by
    intro x hx
    rw [show w' x=w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x from rfl,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw _ (herase x hx))).trans
      (assignedSecondCoefficient_norm_le_one source J₁ J₂ base₁ base₂ a₁ a₂ ha₁ ha₂ x (hsub hx))
  have hc' : ∀ x∈S,(actualSecondChild p u v x).2.1∈labels ∧ (actualSecondChild p u v x).2.2∈rows := by
    intro x hx
    simpa only [actualSecondChild_erase] using hchild (eraseSecondSlots x) (herase x hx)
  have he := varyingAssignedSource_sum_marks source J₁ J₂ base₁ base₂ L₁ L₂ hL₁ hL₂ a₁ a₂ w
    (fun x=>F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x)))
  simp only [actualSecondChild_erase,←mul_assoc] at he
  simp only [←mul_assoc]
  rw [he]
  exact actual_second_weighted_count p hp hpr hcop hinj u v S hs' labels rows hc' K ho
    (by omega) w' hw' F G

end SevenEighths.InverseMoment

end

end OAI

end Source2400

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondVaryingSupported.lean; sha256: becc9e336e902e415ecf34739f1acf1fef1025fcdc089fc2f8890bd11f319059 -/
section Source2401
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_supported_varying_lists_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : MarkedSecondSource ι Jo 0 → Eis) (z : SecondRayIndex)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ → Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ base₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ base₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (phase : MarkedSecondSource ι Jo 0 → ℂ) (hphase : ∀ x ∈ source, ‖phase x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource
          source J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource
          source J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows G γ) := by
  let S := source.filter (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x ≠ 0)
  have hsub : S ⊆ source := Finset.filter_subset _ _
  have he : (∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))) =
    ∑ x ∈ S, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x)) := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have hz : actualSecondSignedWeight p hp hcop hg Ψ (m x) z x = 0 := by
      by_contra hh
      exact hnx (Finset.mem_filter.mpr ⟨hx,hh⟩)
    simp only [hz,zero_mul]
  rw [he]
  have hb := actual_second_varying_lists_weighted_count p hp hpr hcop hinj u v S
    (hs.mono p hsub) J₁ J₂ base₁ base₂ L₁ L₂
    (fun x hx=>hL₁ x (hsub hx)) (fun x hx=>hL₂ x (hsub hx)) a₁ a₂ ha₁ ha₂ (labels.filter Squarefree) rows
    (by
      intro x hx
      have hx0 := hsub hx
      refine ⟨Finset.mem_filter.mpr ⟨(hchild x hx0).1,?_⟩,(hchild x hx0).2⟩
      exact actual_second_nonzero_weight_squarefree p hp hcop hg Ψ (m x) z x
        (hs.common_disjoint x hx0) (hs.second_divisor x hx0) (Finset.mem_filter.mp hx).2 u v)
    K ho hJ₁ hJ₂ (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x*phase x)
    (by
      intro x hx
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (actualSecondSignedWeight_norm_le_one p hp hcop hg hinj hc Ψ hΨ (m x) z x)).trans
          (hphase x (hsub hx))) F G
  apply hb.trans
  have hΓ := actualSecondTriples_mono p u v (varyingAssignedSource_mono hsub J₁ J₂ base₁ base₂ L₁ L₂)
  have hsum (P : SecondChild → ℂ) :
      (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource S J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ) ≤
      ∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hΓ
    intro γ _ _
    exact mul_nonneg (tripleDivisorWeight_nonneg K γ) (secondLabelEnergy_nonneg _ _ _ _ _)
  exact mul_le_mul (Real.sqrt_le_sqrt (hsum F)) (Real.sqrt_le_sqrt (hsum G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end SevenEighths.InverseMoment

end OAI

end Source2401

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondDeletedModeEnergy.lean; sha256: d5d7b8c156e125beb37c1094c18de7a8c30bafa4f22adc2a15190f3809bbc8ae -/
section Source2402
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_mode_branch_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ lists₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ lists₂ i, ‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x ∈ source,(actualSecondChild p u v x).2.1 ∈ labels)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source,‖w x‖ ≤ 1) :
    ‖∑ x ∈ source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ lists₁ lists₂
        (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ lists₁ lists₂
        (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ) := by
  let phase := fun x => w x * secondModeOuter p x Ψ m z G E V B X t
  have hphase : ∀ x ∈ source,‖phase x‖ ≤ 1 := by
    intro x hx
    simpa only [phase,norm_mul,secondModeOuter,secondOuterPhase_norm,mul_one] using hw x hx
  have hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ nonzeroChildFrequencyBall 1 R := by
    intro x hx
    exact ⟨hlabels x hx,(actual_second_row_ball p hp hpr x u v R).mp (hrows x hx)⟩
  have he := actual_second_supported_varying_lists_energy p hp hcop hg hpr hinj hc
    u v source hs Ψ hΨ (fun x => m*ConcretePrimeRowBridge.idealGenerator x.quotient) z
    J₁ J₂ lists₁ lists₂ (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)
    (fun _ _ _ _=>Finset.sdiff_subset) (fun _ _ _ _=>Finset.sdiff_subset) a₁ a₂ ha₁ ha₂ labels (nonzeroChildFrequencyBall 1 R) hchild
    K ho hJ₁ hJ₂ phase hphase
    (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t)
    (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t)
  apply le_trans (le_of_eq ?_) he
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [secondModeBranch_parent_lists_restore p hp hcop hg hpr x (hs.admissible x hx)
    (hs.second_divisor x hx) u v (deleted₁ x) (deleted₂ x) (hd₁ x hx) (hd₂ x hx)]
  dsimp only [phase]
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2402

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondWholeMass.lean; sha256: 2ee36e75715446b40947c7324ea84e5e63ef652f2297e695e0f1a51410f4707b -/
section Source2403
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem actualSecondChild_outer_units {Jo Jn : ℕ} (u v : Eisˣ)
    (x : MarkedSecondSource ι Jo Jn) :
    (actualSecondChild p u v x).1 = (actualSecondChild p 1 1 x).1 := rfl

theorem actualSecondChild_label_units {Jo Jn : ℕ} (u v : Eisˣ)
    (x : MarkedSecondSource ι Jo Jn) :
    (actualSecondChild p u v x).2.1 = (actualSecondChild p 1 1 x).2.1 := rfl

theorem actualSecondTriples_units {Jo Jn : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo Jn)) :
    actualSecondTriples p u v source = actualSecondTriples p 1 1 source := rfl

theorem assigned_second_triples_subset {Jo : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂) ⊆
      actualSecondTriples p 1 1 source := by
  intro γ hγ
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ L₁ L₂ x).mp hx
  exact Finset.mem_image.mpr ⟨y,hy,rfl⟩

theorem assigned_second_mass_le_original {Jo : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (K : ℕ) :
    (∑ γ∈actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),tripleDivisorWeight K γ) ≤
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (assigned_second_triples_subset p u v source J₁ J₂ L₁ L₂)
    (fun γ _ _ => tripleDivisorWeight_nonneg K γ)

end
end SevenEighths.InverseMoment

end OAI

end Source2403

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondDeletedOriginalBound.lean; sha256: 6bd280792da08363aa0adfe055e11b5c8215b868f288b4fbe458d130e19ee286 -/
section Source2404
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

theorem actual_second_deleted_mode_original_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
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
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤ A * ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  have hlabels' : ∀ x∈source,(actualSecondChild p u v x).2.1 ∈ labels := by
    intro x hx
    rw [actualSecondChild_label_units]
    exact hlabels x hx
  have hΓ := (actualSecondTriples_mono p u v
    (show varyingAssignedSource source J₁ J₂ lists₁ lists₂
      (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)⊆
      assignedSecondSource source J₁ J₂ lists₁ lists₂ from Finset.filter_subset _ _)).trans
      (assigned_second_triples_subset p u v source J₁ J₂ lists₁ lists₂)
  apply (actual_second_deleted_mode_branch_energy p hp hcop hg hpr hinj hc u v source hs pool Ψ hΨ m z
    slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ hd₁ hd₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels
    hlabels' hrows K ho hJ₁ hJ₂ w hw).trans
  apply (second_geometric_energy_of_bound K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
    _ _ _ A hA (fun γ hγ => hright γ (hΓ hγ)) (fun γ hγ => hleft γ (hΓ hγ))).trans
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg hΓ (fun γ _ _=>tripleDivisorWeight_nonneg K γ)) hA

end
end SevenEighths.InverseMoment

end OAI

end Source2404

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondDeletedAllModes.lean; sha256: ab553d0c6965ef1d98b928c8379c398442e8b323ee34b60bf585b82f09424e48 -/
section Source2405
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedAllModesUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondDeletedFullModeSum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
    ∑ x∈secondSourceSector source sector uv,
      actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
          ω₁ ω₂ G E V B X t

theorem secondDeletedFullModeSum_physical {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) :
    secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      ω₁ ω₂ G E V B X w t =
    ∑ uv : Eisˣ × Eisˣ,∑ x∈secondSourceSector source sector uv,
      (w x*actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
        ∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
            ω₁ ω₂ G E V B X t := by
  unfold secondDeletedFullModeSum
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

theorem actual_second_deleted_all_modes_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
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
    ‖secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      ω₁ ω₂ G E V B X w t‖ ≤
    36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  let mass := ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hbound (uv : Eisˣ × Eisˣ) (J₁ : Finset σ) (hJ₁ : J₁∈slots₁.powerset)
      (J₂ : Finset σ) (hJ₂ : J₂∈slots₂.powerset) :
      ‖∑ x∈secondSourceSector source sector uv,
        actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*w x*
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
            ω₁ ω₂ G E V B X t‖ ≤ A*mass := by
    have hsub : secondSourceSector source sector uv ⊆ source := Finset.filter_subset _ _
    have ht := actualSecondTriples_mono p 1 1 hsub
    have h := actual_second_deleted_mode_original_bound p hp hcop hg hpr hinj hc uv.1 uv.2
      (secondSourceSector source sector uv) (hs.mono p hsub) pool Ψ hΨ m z
      slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      (fun x hx=>hd₁ x (hsub hx)) (fun x hx=>hd₂ x (hsub hx))
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
            secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
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

end Source2405

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondDeletedAllIntegral.lean; sha256: 5e40bb81923e3459a2fb3ddf89f05299171ca4791c088cc5049615012a6b65c3 -/
section Source2406
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedAllIntegralUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_all_modes_integral
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
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
    ‖∫ t : Frequency × (Fin 6 → ℝ),density t*secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      ω₁ ω₂ G E V B X w t‖ ≤
    (36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
      ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖ := by
  let C := 36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
    ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hb (t : Frequency × (Fin 6 → ℝ)) :
      ‖secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
        ω₁ ω₂ G E V B X w t‖ ≤ C*(tripleHeight J t.1*coordinateHeight J t.2) := by
    have hh := actual_second_deleted_all_modes_bound p hp hcop hg hpr hinj hc source hs sector pool Ψ hΨ m z
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ hd₁ hd₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels hlabels hrows
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

end Source2406

/- Original source: OAI/NumberTheory/DirichletL/Descent/DensityAssembly.lean; sha256: 84849740e88dd7401458fb19f09d648e8b869478567874a94f832bad14b47b2d -/
section Source2407
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

theorem integrable_density_mode {ι : Type*} [Fintype ι]
    (D : Frequency × (ι → ℝ) → ℂ) (hD : Integrable D) (a₁ a₂ ak y : ι → ℝ) :
    Integrable (fun z : Frequency × (ι → ℝ) => D z *
      pureProfileMode a₁ a₂ ak y z.1 z.2) := by
  have hc : Continuous (fun z : Frequency × (ι → ℝ) => pureProfileMode a₁ a₂ ak y z.1 z.2) := by
    unfold pureProfileMode logPhase
    fun_prop
  exact hD.mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => (pureProfileMode_norm a₁ a₂ ak y z.1 z.2).le))

theorem density_finite_sum {ι κ : Type*} [Fintype ι] (s : Finset κ)
    (D : Frequency × (ι → ℝ) → ℂ) (hD : Integrable D) (a₁ a₂ ak : ι → ℝ)
    (c : κ → ℂ) (y : κ → ι → ℝ) :
    (∑ k ∈ s,c k * ∫ z : Frequency × (ι → ℝ),D z*pureProfileMode a₁ a₂ ak (y k) z.1 z.2) =
    ∫ z : Frequency × (ι → ℝ),D z * ∑ k ∈ s,c k*pureProfileMode a₁ a₂ ak (y k) z.1 z.2 := by
  simp only [← integral_const_mul]
  rw [← integral_finsetSum s (fun k hk => (integrable_density_mode D hD a₁ a₂ ak (y k)).const_mul (c k))]
  apply integral_congr_ae
  filter_upwards with z
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2407

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondVaryingDensity.lean; sha256: d909a354f2c4215230c42cf49ff81de5efb69dc9ca6a6032f5187fe3a955d140 -/
section Source2408
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actualSecondVaryingFreshRows_integral_density {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : κ → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density)
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), density v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        density v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  have hindexed : (∑ j∈source,w j*actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ∑ j∈secondProfileIndices source F x,
        (w j.1*secondActualCoefficient p hp hcop hg (x j.1) slots₁ slots₂
          (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2)*
        secondNormProfile (fun z=>star (W₁ (z/(G₀*V₀*X₀))))
          (fun z=>W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _=>1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2) := by
    simp_rw [actualSecondProfileRow_eq_whole]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  rw [hindexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← density_finite_sum _ density hDensity,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj]
  ring

theorem actualSecondVaryingFreshRows_normalized_density {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : κ → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density) (normalization : ℂ)
    (he : ∀ j ∈ secondProfileIndices source F x,
      normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), density v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    normalization * (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        density v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  have hindexed : (∑ j∈source,w j*actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ∑ j∈secondProfileIndices source F x,
        (w j.1*secondActualCoefficient p hp hcop hg (x j.1) slots₁ slots₂
          (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2)*
        secondNormProfile (fun z=>star (W₁ (z/(G₀*V₀*X₀))))
          (fun z=>W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _=>1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2) := by
    simp_rw [actualSecondProfileRow_eq_whole]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  rw [hindexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← density_finite_sum _ density hDensity]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
        slots₁ slots₂ (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2) *
        (normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
          (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2)) := by ring
    _ = _ := by rw [he j hj]; ring

end
end SevenEighths.InverseMoment

end OAI

end Source2408

/- Original source: OAI/NumberTheory/DirichletL/Inversion/SecondProfileUniform.lean; sha256: a0ba1c87f05fa70e796c2a06a9e5cbfecfa7eb2ef97fbc3e939c268e430982f1 -/
section Source2409
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment
open SevenEighths.InverseInitialProfile
open SevenEighths.InverseAmbientProfileTower
namespace SevenEighths.InverseSecondProfileUniform

def rooted (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  InverseClippingProfiles.rootSchwartz g M 0 1 0 a 0 zero_lt_one (by simp) hg

@[simp] theorem rooted_apply (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (y : ℝ) :
    rooted g M a hg y = (Real.exp (a*y) : ℂ)*g y := by
  simp [rooted, InverseClippingProfiles.rootedWindow, InverseClippingProfiles.logWindow]

theorem rooted_support (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) :
    Function.support (rooted g M a hg) ⊆ Set.Icc (-M) M := by
  intro y hy
  exact hg (by simpa using hy)

def translated (g : 𝓢(ℝ, ℂ)) (ρ : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compSubConstCLM ℂ (-ρ) g

@[simp] theorem translated_apply (g : 𝓢(ℝ, ℂ)) (ρ y : ℝ) :
    translated g ρ y = g (y+ρ) := by simp [translated]

theorem fourier_translated (g : 𝓢(ℝ, ℂ)) (ρ t : ℝ) :
    (𝓕 (translated g ρ)) t = logPhase t ρ * (𝓕 g) t := by
  rw [SchwartzMap.fourier_coe]
  have he : (translated g ρ : ℝ → ℂ) = fun y => g (y+ρ) := by ext y; simp
  rw [he, InverseClippingProfiles.fourier_translate, ← SchwartzMap.fourier_coe]

def normalization (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) : ℝ :=
  Real.exp (-6*L - ∑ i, InverseClippingProfiles.secondBalancedSlope i*ρ i +
    (Real.log c₁+Real.log c₂)/2)

def density (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 6)) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    fullProfileDensity (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

theorem density_formula (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 6)) :
    density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p =
      (normalization ρ c₁ c₂ L : ℂ) *
        (sourceDensity g₁ c₁ θ₁ p.1.1 * (sourceDensity g₂ c₂ θ₂ p.1.2.1 * b₃ p.1.2.2)) *
        (∏ i, logPhase (p.2 i) (ρ i) * (𝓕 (g i)) (p.2 i)) := by
  simp only [density, fullProfileDensity, tripleCoefficient, coordinateDensity,
    fourier_translated, fourier_clippedTwist]
  ring

private theorem fourier_twist (g : 𝓢(ℝ, ℂ)) (θ t : ℝ) :
    (𝓕 (frequencyTwist g θ)) t = (𝓕 g) (t-θ) := by
  rw [SchwartzMap.fourier_coe]
  have he : (frequencyTwist g θ : ℝ → ℂ) = fun y => logPhase θ y * g y := by
    ext y
    exact frequencyTwist_apply g θ y
  rw [he, InverseClippingProfiles.fourier_phase_shift, ← SchwartzMap.fourier_coe]

theorem density_norm (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 6)) :
    ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖ = normalization ρ c₁ c₂ L *
      ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖ := by
  rw [density_formula]
  simp only [norm_mul, norm_prod, sourceDensity_norm, logPhase_norm, one_mul,
    Complex.norm_real, Real.norm_eq_abs, normalization,
    abs_of_pos (Real.exp_pos _), twistedFullDensity, fullProfileDensity,
    tripleCoefficient, coordinateDensity, fourier_twist]
  ring

theorem density_joint_measurable (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun z : ((Fin 6 → ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × ℝ) × Ambient (Fin 6) =>
      density g g₁ g₂ b₃ z.1.1 z.1.2.1.1 z.1.2.1.2 z.1.2.2.1.1 z.1.2.2.1.2 z.1.2.2.2 z.2) := by
  simp_rw [density_formula]
  apply Measurable.stronglyMeasurable
  unfold normalization sourceDensity logPhase
  have h1 := (𝓕 g₁ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h2 := (𝓕 g₂ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h3 := b₃.continuous.measurable
  have hu (i : Fin 6) := (𝓕 (g i) : 𝓢(ℝ, ℂ)).continuous.measurable
  have he := Complex.continuous_exp.measurable
  fun_prop

theorem normalization_bound (B : Fin 6 → ℝ) (b : ℝ)
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (hρ : ∀ i, |ρ i| ≤ B i)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁b : c₁ ≤ b) (hc₂b : c₂ ≤ b) (hL : 0 ≤ L) :
    normalization ρ c₁ c₂ L ≤
      Real.exp ((∑ i, |InverseClippingProfiles.secondBalancedSlope i| *B i)+Real.log b) := by
  unfold normalization
  apply Real.exp_le_exp.mpr
  have hs : -(∑ i, InverseClippingProfiles.secondBalancedSlope i*ρ i) ≤
      ∑ i, |InverseClippingProfiles.secondBalancedSlope i| *B i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |InverseClippingProfiles.secondBalancedSlope i*ρ i| := neg_le_abs _
      _ = |InverseClippingProfiles.secondBalancedSlope i| *|ρ i| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hρ i) (abs_nonneg _)
  have h1 := Real.log_le_log hc₁ hc₁b
  have h2 := Real.log_le_log hc₂ hc₂b
  linarith

theorem density_weighted_integrable (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Ambient (Fin 6) => ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) := by
  simp_rw [density_norm]
  convert (InverseAmbientProfileTower.fullProfileDensity_weighted_integrable g
    (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ J).const_mul
      (normalization ρ c₁ c₂ L) using 1
  funext p
  unfold twistedFullDensity
  ring

private theorem radial_common_box (Φ : 𝓢(ℝ, ℂ)) (M : Fin 6 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ (V : Fin 6 → ℝ → ℂ), (∀ i y, V i y ≠ 0 → |y| ≤ M i) →
        ∀ y : Fin 6 → ℝ,
        (∏ i, V i (y i))*paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)) =
          ∫ t : ℝ, (∏ i, V i (y i)*logPhase t (secondKernelSlope i*y i))*b₃ t) ∧
      (1+R)^A * (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) ≤ C := by
  let box : Fin 6 → ℝ → ℂ := fun i y => if |y| ≤ M i then 1 else 0
  have hb : ∀ i y, box i y ≠ 0 → |y| ≤ M i := by
    intro i y h
    simpa [box] using h
  obtain ⟨C,hC,hs⟩ := paperRadialFourier_log_separation_envelope Φ box
    secondKernelSlope M hM hb A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,he,_,hm,_⟩ := hs R hR
  refine ⟨b₃,?_,hm⟩
  intro V hV y
  simp only [Finset.prod_mul_distrib]
  by_cases hz : (∏ i, V i (y i)) = 0
  · simp [hz]
  · have hall (i : Fin 6) : V i (y i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)
    have hbox (i : Fin 6) : box i (y i) = 1 := by simp [box, hV i _ (hall i)]
    have h := he y
    simp only [hbox, one_mul, Finset.prod_const_one] at h
    rw [h, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring

theorem translated_box (g : 𝓢(ℝ, ℂ)) (M B ρ : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (hρ : |ρ| ≤ B)
    {y : ℝ} (hy : translated g ρ y ≠ 0) : |y| ≤ M+B := by
  have h := hg (show g (y+ρ) ≠ 0 from by simpa only [translated_apply] using hy)
  have hr := abs_le.mp hρ
  apply abs_le.mpr
  constructor <;> linarith [h.1,h.2,hr.1,hr.2]

theorem density_weighted_integral (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Ambient (Fin 6), ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) = normalization ρ c₁ c₂ L *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₁ θ₁)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₂ θ₂)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
        (∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖) := by
  simp_rw [density_norm]
  have he (p : Ambient (Fin 6)) :
      ambientWeight J p * (normalization ρ c₁ c₂ L *
        ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖) =
      normalization ρ c₁ c₂ L * (tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖fullProfileDensity g (𝓕 (frequencyTwist g₁ θ₁))
          (𝓕 (frequencyTwist g₂ θ₂)) b₃ p‖) := by
    unfold ambientWeight tripleHeight coordinateHeight twistedFullDensity
    ring
  simp_rw [he]
  rw [integral_const_mul, InverseMoment.fullProfileDensity_weighted_integral]
  simp only [tripleHeight]
  rw [tripleCoefficient_weighted_integral]
  ring

def profile (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    ((∏ i, translated (g i) (ρ i) (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, secondLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, secondRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)))

def requiredOuterOrder (J : ℕ) : ℕ := J+2*InverseClippingProfiles.momentOrder J

theorem common_measure (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hg : ∀ i, Function.support (g i) ⊆ Set.Icc (-M i) (M i)) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 0 < c₁ → 0 < c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 6 → ℝ, profile g g₁ g₂ Φ ρ c₁ c₂ θ₁ θ₂ R L y =
        ∫ p : Ambient (Fin 6), density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 6) => ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 6), ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  obtain ⟨C₃,hC₃,hsep⟩ := radial_common_box Φ (fun i => M i+B i)
    (fun i => add_nonneg (hM i) (hB i)) A J
  obtain ⟨C₁,hC₁,h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂,hC₂,h₂⟩ := frequencyTwist_fourier_moment J g₂
  let D := ∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖
  let E := Real.exp ((∑ i, |InverseClippingProfiles.secondBalancedSlope i| * B i)+Real.log b)
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i _ => integral_nonneg (fun _ => by positivity))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨E*C₁*C₂*C₃*D, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃,he,hm⟩ := hsep R hR
  refine ⟨b₃,?_⟩
  intro ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  refine ⟨?_, density_weighted_integrable _ _ _ _ _ _ _ _ _ _ _, ?_⟩
  · intro y
    have hb : ∀ i z, translated (g i) (ρ i) z ≠ 0 → |z| ≤ M i+B i :=
      fun i z hz => translated_box (g i) (M i) (B i) (ρ i) (hg i) (hρ i) hz
    have hid := descent_profile_identity (clippedTwist g₁ c₁ θ₁) (clippedTwist g₂ c₂ θ₂)
      Φ (fun i => translated (g i) (ρ i)) secondLeftSlope secondRightSlope secondKernelSlope
      R b₃ (he _ hb) y
    have habs := profile_integral_coordinate_absorption (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃
      secondLeftSlope secondRightSlope secondKernelSlope y
    simp only [profileMode] at habs
    unfold profile
    rw [hid, habs, ← full_density_mode_fubini, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    unfold density
    ring
  · rw [density_weighted_integral]
    have h12 := mul_le_mul (h₁ θ₁) (h₂ θ₂)
      (integral_nonneg (fun _ => by positivity)) (by positivity)
    have h123 := mul_le_mul h12 hm (by positivity) (by positivity)
    have hd := mul_le_mul_of_nonneg_right h123 hD
    have hn := normalization_bound B b ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
    have hh := mul_le_mul hn hd (by positivity) hE
    convert hh using 1 <;>
      (dsimp only [InverseClippingProfiles.momentOrder, E, D]; ring)

theorem balanced_exponential_identity (ρ y : Fin 6 → ℝ) (c₁ c₂ L : ℝ) :
    normalization ρ c₁ c₂ L *
      (∏ i, Real.exp (InverseClippingProfiles.secondBalancedSlope i*(y i+ρ i))) *
      Real.exp (-(1/2:ℝ)*((∑ i, secondLeftSlope i*y i)+Real.log c₁)) *
      Real.exp (-(1/2:ℝ)*((∑ i, secondRightSlope i*y i)+Real.log c₂)) =
      Real.exp (-6*L)*Real.exp (InverseClippingProfiles.secondRootExponent y) := by
  rw [normalization, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [InverseClippingProfiles.secondBalancedSlope,
    InverseClippingProfiles.secondRootExponent, secondLeftSlope, secondRightSlope,
    Fin.sum_univ_succ]
  ring

def positiveSource (g : 𝓢(ℝ, ℂ)) (c θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x)*g (Real.log x+Real.log c)

theorem positiveSource_logSchwartz (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (θ : ℝ) :
    positiveSource (CubicReflectionKernel.logSchwartz W a b ha hs hW) c θ x =
      clippedSource W c θ x := by
  simp only [positiveSource, CubicReflectionKernel.logSchwartz_apply,
    Real.exp_add, Real.exp_log hc, Real.exp_log hx, clippedSource]
  rw [mul_comm x c]

theorem balanced_profile_identity
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M : Fin 6 → ℝ) (m₁ m₂ : ℝ)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂)
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) :
    profile (fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i))
      (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂)
      Φ ρ c₁ c₂ θ₁ θ₂ R L y =
      (Real.exp (-6*L) : ℂ) * secondPoissonProfile
        (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
        Φ (fun i y => U i (y+ρ i)) R y := by
  have he := congrArg (fun x : ℝ => (x : ℂ)) (balanced_exponential_identity ρ y c₁ c₂ L)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod] at he
  unfold profile secondPoissonProfile
  rw [InverseClippingProfiles.secondRootWindows_prod]
  simp only [translated_apply, clippedTwist_apply, rooted_apply, positiveSource, Real.log_exp,
    Finset.prod_mul_distrib]
  linear_combination
    (∏ i, U i (y i+ρ i)) * logPhase θ₁ (∑ i, secondLeftSlope i*y i) *
    g₁ ((∑ i, secondLeftSlope i*y i)+Real.log c₁) *
    logPhase θ₂ (∑ i, secondRightSlope i*y i) *
    g₂ ((∑ i, secondRightSlope i*y i)+Real.log c₂) *
    paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)) * he

theorem second_profile_common_measure
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 6 → ℝ,
        (Real.exp (-6*L) : ℂ) * secondPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ (fun i y => U i (y+ρ i)) R y =
        ∫ p : Ambient (Fin 6), density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 6) => ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 6), ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C,hC,hs⟩ := common_measure
    (fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i))
    (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂) Φ M B b hM hB
    (fun i => rooted_support _ _ _ _) A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,hb₃⟩ := hs R hR
  refine ⟨b₃,?_⟩
  intro ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have h := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ (zero_lt_one.trans_le hc₁)
    (zero_lt_one.trans_le hc₂) hc₁b hc₂b hL
  refine ⟨?_,h.2⟩
  intro y
  rw [← balanced_profile_identity U g₁ g₂ Φ M m₁ m₂ hU h₁ h₂]
  exact h.1 y

def densityTower {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (z : Ambient ι × Ambient (Fin 6)) : ℂ :=
  fullProfileDensity outer b₁ b₂ b₃ z.1 *
    density g g₁ g₂ c₃ ρ c₁ c₂ (inheritedLeft i z.1) (inheritedRight j z.1) L z.2

theorem densityTower_joint_measurable {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) :
    StronglyMeasurable (densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L) := by
  unfold densityTower
  apply StronglyMeasurable.mul
  · exact ((InverseAmbientProfileTower.fullProfileDensity_continuous outer b₁ b₂ b₃).comp
      continuous_fst).stronglyMeasurable
  · have hm : Measurable (fun z : Ambient ι × Ambient (Fin 6) =>
        ((ρ,(c₁,c₂),(inheritedLeft i z.1,inheritedRight j z.1),L),z.2)) := by
      unfold inheritedLeft inheritedRight
      fun_prop
    exact (density_joint_measurable g g₁ g₂ c₃).comp_measurable hm

theorem densityTower_norm {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (z : Ambient ι × Ambient (Fin 6)) :
    ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖ =
      normalization ρ c₁ c₂ L *
        ‖InverseAmbientProfileTower.towerDensity i j outer b₁ b₂ b₃ g g₁ g₂ c₃ z‖ := by
  simp only [densityTower, InverseAmbientProfileTower.towerDensity, norm_mul, density_norm]
  ring

theorem densityTower_weighted_integrable {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (J : ℕ) :
    Integrable (fun z : Ambient ι × Ambient (Fin 6) =>
      ambientWeight J z.1 * ambientWeight J z.2 *
        ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖) := by
  obtain ⟨C,hC,h⟩ := InverseAmbientProfileTower.towerDensity_weighted (ι := ι) J g g₁ g₂ c₃
  convert (h i j outer b₁ b₂ b₃).1.const_mul (normalization ρ c₁ c₂ L) using 1
  funext z
  rw [densityTower_norm]
  ring

private theorem tower_bound_from_inner {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L C R : ℝ) (hC : 0 ≤ C) (_hR : 0 < R) (A J : ℕ)
    (hb : ∀ θ₁ θ₂ : ℝ, (1+R)^A * (∫ q : Ambient (Fin 6), ambientWeight J q *
        ‖density g g₁ g₂ c₃ ρ c₁ c₂ θ₁ θ₂ L q‖) ≤
      C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
        (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J))) :
    (1+R)^A * (∫ z : Ambient ι × Ambient (Fin 6),
      ambientWeight J z.1 * ambientWeight J z.2 *
        ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖) ≤
      C * (∫ p : Ambient ι, ambientWeight (requiredOuterOrder J) p *
        ‖fullProfileDensity outer b₁ b₂ b₃ p‖) := by
  let f := fun z : Ambient ι × Ambient (Fin 6) =>
    ambientWeight J z.1 * ambientWeight J z.2 *
      ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖
  have hi : Integrable f := densityTower_weighted_integrable i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L J
  have hi' : Integrable (fun z : Ambient ι × Ambient (Fin 6) => (1+R)^A*f z) := hi.const_mul _
  have hout := (InverseAmbientProfileTower.fullProfileDensity_weighted_integrable
    outer b₁ b₂ b₃ (requiredOuterOrder J)).const_mul C
  change (1+R)^A*(∫ z, f z) ≤ _
  rw [← integral_const_mul]
  rw [show (∫ z : Ambient ι × Ambient (Fin 6), (1+R)^A*f z) =
      ∫ p : Ambient ι, ∫ q : Ambient (Fin 6), (1+R)^A*f (p,q) by
    simpa only [Measure.volume_eq_prod] using integral_prod _ hi']
  rw [← integral_const_mul]
  have hip : Integrable (fun z : Ambient ι × Ambient (Fin 6) => (1+R)^A*f z) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hi'
  apply integral_mono hip.integral_prod_left hout
  intro p
  dsimp only
  have he : (∫ q : Ambient (Fin 6), (1+R)^A*f (p,q)) =
      ambientWeight J p * ‖fullProfileDensity outer b₁ b₂ b₃ p‖ *
        ((1+R)^A * ∫ q : Ambient (Fin 6), ambientWeight J q *
          ‖density g g₁ g₂ c₃ ρ c₁ c₂ (inheritedLeft i p) (inheritedRight j p) L q‖) := by
    simp only [f, densityTower, norm_mul]
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with q
    ring
  rw [he]
  have hw := inherited_pair_weight_bound i j J (InverseClippingProfiles.momentOrder J) p
  have hp : 0 ≤ ambientWeight J p := zero_le_one.trans (ambientWeight_one_le J p)
  calc
    _ ≤ (ambientWeight J p * ‖fullProfileDensity outer b₁ b₂ b₃ p‖) *
        (C*((1+‖inheritedLeft i p‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖inheritedRight j p‖)^(InverseClippingProfiles.momentOrder J))) :=
      mul_le_mul_of_nonneg_left (hb _ _) (mul_nonneg hp (norm_nonneg _))
    _ = (C*‖fullProfileDensity outer b₁ b₂ b₃ p‖) *
        (ambientWeight J p * ((1+‖inheritedLeft i p‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖inheritedRight j p‖)^(InverseClippingProfiles.momentOrder J))) := by ring
    _ ≤ (C*‖fullProfileDensity outer b₁ b₂ b₃ p‖) * ambientWeight (requiredOuterOrder J) p :=
      mul_le_mul_of_nonneg_left hw (mul_nonneg hC (norm_nonneg _))
    _ = _ := by ring

theorem second_profile_tower_uniform {ι : Type*} [Fintype ι]
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ c₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ (θ₁ θ₂ : ℝ) (y : Fin 6 → ℝ),
        (Real.exp (-6*L) : ℂ) * secondPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ (fun i y => U i (y+ρ i)) R y =
        ∫ p : Ambient (Fin 6), density G f₁ f₂ c₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      (∀ (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
        Integrable (fun z : Ambient ι × Ambient (Fin 6) =>
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖densityTower i j outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ∧
        (1+R)^A * (∫ z : Ambient ι × Ambient (Fin 6),
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖densityTower i j outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ≤
          C * (∫ p : Ambient ι, ambientWeight (requiredOuterOrder J) p *
            ‖fullProfileDensity outer b₁ b₂ b₃ p‖)) := by
  dsimp only
  obtain ⟨C,hC,hs⟩ := second_profile_common_measure U g₁ g₂ Φ M B m₁ m₂ b hM hB hU h₁ h₂ A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨c₃,hc₃⟩ := hs R hR
  refine ⟨c₃,?_⟩
  intro ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  refine ⟨fun θ₁ θ₂ => (hc₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL).1, ?_⟩
  intro i j outer b₁ b₂ b₃
  refine ⟨densityTower_weighted_integrable i j outer b₁ b₂ b₃ _ _ _ c₃ ρ c₁ c₂ L J, ?_⟩
  exact tower_bound_from_inner i j outer b₁ b₂ b₃ _ _ _ c₃ ρ c₁ c₂ L C R hC hR A J
    (fun θ₁ θ₂ => (hc₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL).2.2)

theorem densityTower_fubini {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ)
    (F : Ambient ι × Ambient (Fin 6) → ℂ) (hF : StronglyMeasurable F) (J : ℕ)
    (hbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    (∫ z, densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z * F z) =
      ∫ p, ∫ q, densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L (p,q) * F (p,q) :=
  density_test_fubini _ F
    (densityTower_joint_measurable i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L) hF J
    (densityTower_weighted_integrable i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L J) hbound

theorem actual_child_height_weight_bound (J K : ℕ) (p : Ambient (Fin 6)) :
    ambientWeight J p *
      ((1+‖profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 4‖)^K *
       (1+‖profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 5‖)^K) ≤
      ambientWeight (J+2*K) p := by
  simpa only [second_inherited_left_eq, second_inherited_right_eq, norm_neg] using
    inherited_pair_weight_bound (4 : Fin 6) 5 J K p

theorem normalization_eta_log (Z η : ℝ) (hZ : 0 < Z) :
    Real.exp (-6*(η*Real.log Z)) = Z^(-6*η) := by
  rw [Real.rpow_def_of_pos hZ]
  congr 1
  ring

theorem fresh_physical_profile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ Y L : ℝ)
    (hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (ω₁ ω₂ : ℝ → ℂ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hω₁ : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) ≠ 0 → ω₁ (q 4/X₀) = 1)
    (hω₂ : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) ≠ 0 → ω₂ (q 5/X₀) = 1)
    (hcut : ω₁ (q 4/X₀) ≠ 0 → ω₂ (q 5/X₀) ≠ 0 →
      ∀ i, V i (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i) = 1) :
    (Real.exp (-6*L) : ℂ) * secondNormProfile
      (fun x => W₁ (x/(G₀*V₀*X₀))) (fun x => W₂ (x/(G₀*V₀*X₀)))
      Φ (fun _ _ => 1) Y q =
      ((E₀*V₀*X₀ : ℝ) : ℂ)⁻¹ * (ω₁ (q 4/X₀)*ω₂ (q 5/X₀)) *
        ((Real.exp (-6*L) : ℂ)*secondPoissonProfile W₁ W₂ Φ V
          (Y*K₀/(E₀*V₀^2*X₀^2)) (secondRelativeLog q G₀ E₀ V₀ K₀ X₀)) := by
  by_cases hw₁ : ω₁ (q 4/X₀) = 0
  · have hW : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      exact zero_ne_one (hw₁.symm.trans (hω₁ hn))
    simp only [secondNormProfile,hW,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : ω₂ (q 5/X₀) = 0
  · have hW : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      exact zero_ne_one (hw₂.symm.trans (hω₂ hn))
    simp only [secondNormProfile,hW,hw₂,mul_zero,zero_mul,zero_div]
  have hm : secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
    (ω₁ (q 4/X₀)*ω₂ (q 5/X₀))*secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q := by
    by_cases h1 : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [hω₁ h1,hω₂ h2,one_mul]
  rw [hm, secondNormProfile_nominal W₁ W₂ Φ G₀ E₀ V₀ K₀ X₀ Y hG hE hV hK hX q hq]
  change _*( _*(_*secondNormProfile W₁ W₂ Φ (fun _ _ => 1) _
    (secondRelativeNorm q G₀ E₀ V₀ K₀ X₀))) = _
  rw [secondNormProfile_eq_full_of_windows W₁ W₂ Φ V _ _
    (secondRelativeNorm_pos q hq G₀ E₀ V₀ K₀ X₀ hG hE hV hK hX) (hcut hw₁ hw₂)]
  ring_nf
  rfl

theorem retained_clipping_parameter (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) (hret : w (q/Z^N) ≠ 0) :
    let c := Z^(max 0 N-N)
    1 ≤ c ∧ c ≤ b ∧ |Real.log c| ≤ Real.log b ∧
      Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b := by
  dsimp only
  have hc := InverseClippingProfiles.retained_clipped_column w Z N q a b hZ hq ha hb hw hret
  refine ⟨hc.1,hc.2.1,?_,hc.2.2.1⟩
  rw [abs_of_nonneg (Real.log_nonneg hc.1)]
  exact Real.log_le_log (zero_lt_one.trans_le hc.1) hc.2.1

theorem first_second_tower_uniform
    (W₁ W₂ : ℝ → ℂ) (a₀ b₀ : ℝ) (ha₀ : 0 < a₀)
    (hsW₁ : Function.support W₁ ⊆ Set.Icc a₀ b₀)
    (hsW₂ : Function.support W₂ ⊆ Set.Icc a₀ b₀)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ₁ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (MV : Fin 9 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hVS : ∀ i, HasCompactSupport (V i))
    (hMV : ∀ i, 0 ≤ MV i) (hVbox : ∀ i y, V i y ≠ 0 → |y| ≤ MV i)
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ₂ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A₁ A₂ J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    let outer := firstRootSchwartz V hV hVS
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 < R₁ → 0 < R₂ → ∃ b₃ c₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ₁ V R₁ y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 9 → ℝ,
          fullProfileDensity outer b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope
              (t₁,t₂,t₃) u i) (y i))) ∧
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ (θ₁ θ₂ : ℝ) (y : Fin 6 → ℝ),
        (Real.exp (-6*L) : ℂ) * secondPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ₂ (fun i y => U i (y+ρ i)) R₂ y =
        ∫ p : Ambient (Fin 6), density G f₁ f₂ c₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun z : Ambient (Fin 9) × Ambient (Fin 6) =>
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖densityTower 7 8 outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ∧
      (1+R₁)^A₁ * (1+R₂)^A₂ * (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖densityTower 7 8 outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ≤ C := by
  dsimp only
  obtain ⟨C₂,hC₂,hsecond⟩ := second_profile_tower_uniform (ι := Fin 9)
    U g₁ g₂ Φ₂ M B m₁ m₂ b hM hB hU h₁ h₂ A₂ J
  obtain ⟨b₁,b₂,C₁,hC₁,hfirst⟩ := first_full_profile_common_measure
    W₁ W₂ a₀ b₀ ha₀ hsW₁ hsW₂ hW₁ hW₂ Φ₁ V MV hV hVS hMV hVbox A₁ (requiredOuterOrder J)
  refine ⟨b₁,b₂,C₂*C₁,mul_nonneg hC₂ hC₁,?_⟩
  intro R₁ R₂ hR₁ hR₂
  obtain ⟨b₃,he₁,_,hb₁⟩ := hfirst R₁ hR₁
  obtain ⟨c₃,hc₃⟩ := hsecond R₂ hR₂
  refine ⟨b₃,c₃,he₁,?_⟩
  intro ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have h := hc₃ ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have ht := h.2 7 8 (firstRootSchwartz V hV hVS) b₁ b₂ b₃
  refine ⟨h.1,ht.1,?_⟩
  have hh := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ (1+R₁)^A₁ by positivity)
  have hh' := mul_le_mul_of_nonneg_left hb₁ hC₂
  calc
    _ = (1+R₁)^A₁ * ((1+R₂)^A₂ * (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖densityTower 7 8 (firstRootSchwartz V hV hVS) b₁ b₂ b₃
            (fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i))
            (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂)
            c₃ ρ c₁ c₂ L z‖)) := by ring
    _ ≤ (1+R₁)^A₁ * (C₂ * (∫ p : Ambient (Fin 9), ambientWeight (requiredOuterOrder J) p *
        ‖fullProfileDensity (firstRootSchwartz V hV hVS) b₁ b₂ b₃ p‖)) := hh
    _ ≤ C₂*C₁ := by
      simpa only [ambientWeight, tripleHeight, coordinateHeight, mul_assoc,
        mul_left_comm, mul_comm] using hh'

end SevenEighths.InverseSecondProfileUniform

end

end OAI

end Source2409

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondVaryingBalanced.lean; sha256: 2c794279b9de6494baba2089f8af880e7d0fdf75a0a35501f17cb3ec9522830f -/
section Source2410
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_varying_balanced_source (source : Finset κ) (F : Finset ι)
    (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : κ → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6 → ℝ → ℂ)
    (G₀ E₀ V₀ K₀ X₀ Y L : ℝ)
    (hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 6 → ℝ,
      (Real.exp (-6*L):ℂ) * secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ V
        (Y*K₀/(E₀*V₀^2*X₀^2)) y =
      ∫ t : Frequency × (Fin 6 → ℝ), density t *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2)
    (hn : ∀ j ∈ source,(x j).divisor ≠ 0 ∧ (x j).frequency ≠ 0)
    (hω₁ : ∀ j ∈ source, ∀ N ∈ (F\(x j).overlap).powerset,
      W₁ (primeProductNorm p (x j).common*primeProductNorm p (x j).overlap*primeProductNorm p N/(G₀*V₀*X₀)) ≠ 0 →
        ω₁ (primeProductNorm p N/X₀) = 1)
    (hω₂ : ∀ j ∈ source, ∀ N ∈ (F\(x j).overlap).powerset,
      W₂ (primeProductNorm p (x j).common*primeProductNorm p (x j).overlap*primeProductNorm p N/(G₀*V₀*X₀)) ≠ 0 →
        ω₂ (primeProductNorm p N/X₀) = 1)
    (hcut : ∀ j ∈ secondProfileIndices source F x,
      ω₁ (primeProductNorm p j.2.1/X₀) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X₀) ≠ 0 → ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1) :
    (Real.exp (-6*L):ℂ) * (∑ j ∈ source,w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
    ((E₀*V₀*X₀:ℝ):ℂ)⁻¹ * ∫ t : Frequency × (Fin 6 → ℝ),density t *
      ∑ j ∈ source,w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t := by
  apply actualSecondVaryingFreshRows_normalized_density p hp hcop hg source F x w
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ Y G₀ E₀ V₀ K₀ X₀ density hDensity
  intro j hj
  obtain ⟨hjS,hN,hM⟩ := (mem_secondProfileIndices source F x j).mp hj
  have h1 : star (W₁ (primeProductNorm p (x j.1).common*primeProductNorm p (x j.1).overlap*
      primeProductNorm p j.2.1/(G₀*V₀*X₀))) ≠ 0 → star (ω₁ (primeProductNorm p j.2.1/X₀)) = 1 := by
    intro hh
    rw [hω₁ j.1 hjS j.2.1 hN (star_ne_zero.mp hh),star_one]
  have h2 := hω₂ j.1 hjS j.2.2 hM
  have h3 : star (ω₁ (primeProductNorm p j.2.1/X₀)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X₀) ≠ 0 → ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1 :=
    fun ha hb => hcut j hj (star_ne_zero.mp ha) hb
  have he := InverseSecondProfileUniform.fresh_physical_profile
    (fun x => star (W₁ x)) W₂ Φ V G₀ E₀ V₀ K₀ X₀ Y L hG hE hV hK hX
    (fun x => star (ω₁ x)) ω₂ (secondActualNorms p (x j.1) j.2.1 j.2.2)
    (secondActualNorms_pos p hp (x j.1) (hn j.1 hjS).1 (hn j.1 hjS).2 j.2.1 j.2.2)
    (by simpa [secondActualNorms] using h1)
    (by simpa [secondActualNorms] using h2)
    (by simpa [secondActualNorms] using h3)
  rw [hsep] at he
  simpa [secondActualNorms] using he

end
end SevenEighths.InverseMoment

end OAI

end Source2410

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondVaryingPhysical.lean; sha256: 1a672158a901b79e4f0251ef411336c2730c220daa147c0a0d65d4c3cd975771 -/
section Source2411
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondVaryingPhysicalUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
universe u₁ u₂
variable {ι : Type u₁} {σ : Type u₂} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_varying_modes_common_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : MarkedSecondSource ι Jo 0 → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ))
        (w : MarkedSecondSource ι Jo 0 → ℂ),
      (∑ x ∈ source,w x * secondSeparatedPair p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
        slots₁ slots₂ (lists₁ x) (lists₂ x) a₁ a₂ ω₁ ω₂ G E V B X t) =
      ∑ uv : Eisˣ × Eisˣ, ∑ x ∈ secondSourceSector source sector uv, w x *
        ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (lists₁ x) (lists₂ x) a₁ a₂
            ω₁ ω₂ G E V B X t := by
  obtain ⟨sector,hsector⟩ := exists_second_uniform_sectors p hp hcop hg hpr (σ:=σ) source hs
  refine ⟨sector,?_⟩
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t w
  rw [secondSourceSector_partition source sector]
  apply Finset.sum_congr rfl
  intro uv huv
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hx,hxs⟩ := Finset.mem_filter.mp hx
  congr 1
  have hh := hsector x hx
  rw [hxs] at hh
  exact second_inherited_mode_canonical p hp hcop hg x uv.1 uv.2 hh
    pool Ψ m z slots₁ slots₂ (lists₁ x) (lists₂ x) a₁ a₂ ω₁ ω₂ G E V B X t

theorem actual_second_varying_balanced_profile_children
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : MarkedSecondSource ι Jo 0 → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
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
            slots₁ slots₂ (lists₁ x) (lists₂ x) a₁ a₂ W₁ W₂ Φ Y (G*V*X))) =
      ((Y : ℂ)*secondRayCoefficient z*((E*V*X : ℝ):ℂ)⁻¹) *
        ∫ t : Frequency × (Fin 6 → ℝ),density t *
          ∑ uv : Eisˣ × Eisˣ,∑ x ∈ secondSourceSector source sector uv,
            (w x*actualSecondSignedWeight p hp hcop hg Ψ
              (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
            ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
              secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (lists₁ x) (lists₂ x) a₁ a₂
                ω₁ ω₂ G E V B X t := by
  obtain ⟨sector,hsector⟩ := actual_second_varying_modes_common_sectors p hp hcop hg hpr (σ:=σ) source hs
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
  have he := actual_second_varying_balanced_source p hp hcop hg source pool
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
            slots₁ slots₂ (lists₁ x) (lists₂ x) a₁ a₂ W₁ W₂ Φ Y (G*V*X)) := by ring
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

end Source2411

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondDensityAssembly.lean; sha256: 6b251c73dddb74ef18f815ad81fe5092f31db86adb018b24b6cdd887e0ce8f0c -/
section Source2412
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actualSecondFreshRows_integral_density {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density)
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), density v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        density v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  rw [actualSecondProfileRows_eq_indexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← density_finite_sum _ density hDensity,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj]
  ring

theorem actualSecondFreshRows_normalized_density {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density) (normalization : ℂ)
    (he : ∀ j ∈ secondProfileIndices source F x,
      normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), density v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    normalization * (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        density v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  rw [actualSecondProfileRows_eq_indexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← density_finite_sum _ density hDensity]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
        (normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
          (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2)) := by ring
    _ = _ := by rw [he j hj]; ring

end
end SevenEighths.InverseMoment

end OAI

end Source2412

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondBalancedSource.lean; sha256: 7b0bd075db0d9df492059b1f8b9e5d76293d9b28bc5fc0f7ed724c5a52dd21c9 -/
section Source2413
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem balanced_density_integrable (g : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) :
    Integrable (InverseSecondProfileUniform.density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L) := by
  exact (full_density_integrable _ _ _ _).const_mul _

theorem balanced_density_weighted_integrable (g : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun t : Frequency × (Fin 6 → ℝ) => tripleHeight J t.1*coordinateHeight J t.2*
      ‖InverseSecondProfileUniform.density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L t‖) :=
  InverseSecondProfileUniform.density_weighted_integrable g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L J

variable {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_balanced_source (source : Finset κ) (F : Finset ι)
    (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6 → ℝ → ℂ)
    (G₀ E₀ V₀ K₀ X₀ Y L : ℝ)
    (hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 6 → ℝ,
      (Real.exp (-6*L):ℂ) * secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ V
        (Y*K₀/(E₀*V₀^2*X₀^2)) y =
      ∫ t : Frequency × (Fin 6 → ℝ), density t *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2)
    (hn : ∀ j ∈ source,(x j).divisor ≠ 0 ∧ (x j).frequency ≠ 0)
    (hω₁ : ∀ j ∈ source, ∀ N ∈ (F\(x j).overlap).powerset,
      W₁ (primeProductNorm p (x j).common*primeProductNorm p (x j).overlap*primeProductNorm p N/(G₀*V₀*X₀)) ≠ 0 →
        ω₁ (primeProductNorm p N/X₀) = 1)
    (hω₂ : ∀ j ∈ source, ∀ N ∈ (F\(x j).overlap).powerset,
      W₂ (primeProductNorm p (x j).common*primeProductNorm p (x j).overlap*primeProductNorm p N/(G₀*V₀*X₀)) ≠ 0 →
        ω₂ (primeProductNorm p N/X₀) = 1)
    (hcut : ∀ j ∈ secondProfileIndices source F x,
      ω₁ (primeProductNorm p j.2.1/X₀) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X₀) ≠ 0 → ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1) :
    (Real.exp (-6*L):ℂ) * (∑ j ∈ source,w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
    ((E₀*V₀*X₀:ℝ):ℂ)⁻¹ * ∫ t : Frequency × (Fin 6 → ℝ),density t *
      ∑ j ∈ source,w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t := by
  apply actualSecondFreshRows_normalized_density p hp hcop hg source F x w
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ Y G₀ E₀ V₀ K₀ X₀ density hDensity
  intro j hj
  obtain ⟨hjS,hN,hM⟩ := (mem_secondProfileIndices source F x j).mp hj
  have h1 : star (W₁ (primeProductNorm p (x j.1).common*primeProductNorm p (x j.1).overlap*
      primeProductNorm p j.2.1/(G₀*V₀*X₀))) ≠ 0 → star (ω₁ (primeProductNorm p j.2.1/X₀)) = 1 := by
    intro hh
    rw [hω₁ j.1 hjS j.2.1 hN (star_ne_zero.mp hh),star_one]
  have h2 := hω₂ j.1 hjS j.2.2 hM
  have h3 : star (ω₁ (primeProductNorm p j.2.1/X₀)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X₀) ≠ 0 → ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1 :=
    fun ha hb => hcut j hj (star_ne_zero.mp ha) hb
  have he := InverseSecondProfileUniform.fresh_physical_profile
    (fun x => star (W₁ x)) W₂ Φ V G₀ E₀ V₀ K₀ X₀ Y L hG hE hV hK hX
    (fun x => star (ω₁ x)) ω₂ (secondActualNorms p (x j.1) j.2.1 j.2.2)
    (secondActualNorms_pos p hp (x j.1) (hn j.1 hjS).1 (hn j.1 hjS).2 j.2.1 j.2.2)
    (by simpa [secondActualNorms] using h1)
    (by simpa [secondActualNorms] using h2)
    (by simpa [secondActualNorms] using h3)
  rw [hsep] at he
  simpa [secondActualNorms] using he

end
end SevenEighths.InverseMoment

end OAI

end Source2413

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondDeletedPhysicalEnergy.lean; sha256: 73f5d26107b7f6505a6f059abdbf2a0648d76954a4a4d0652b982da2caf7a370 -/
section Source2414
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedPhysicalEnergyUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_physical_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B X Y R L : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K J : ℕ) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
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
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ W₁ W₂ Φ Y (G*V*X))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*X : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
  obtain ⟨sector,hsector⟩ := actual_second_varying_balanced_profile_children p hp hcop hg hpr (σ:=σ) source hs
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w labels K J A hd₁ hd₂ hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have he := hsector pool Ψ m z slots₁ slots₂ (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x) a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
  have hb := actual_second_deleted_all_modes_integral p hp hcop hg hpr hinj hc source hs sector pool Ψ hΨ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ hd₁ hd₂ ha₁ ha₂ ω₁ ω₂ G E V B X R labels hlabels hrows
    K ho hslots₁ hslots₂ w hw A hA J density hWeighted hleft hright
  have hi : (∫ t : Frequency × (Fin 6 → ℝ),density t *
      ∑ uv : Eisˣ × Eisˣ,∑ x∈secondSourceSector source sector uv,
        (w x*actualSecondSignedWeight p hp hcop hg Ψ
          (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
          ∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
            secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
              ω₁ ω₂ G E V B X t) =
      ∫ t : Frequency × (Fin 6 → ℝ),density t*secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ ω₁ ω₂ G E V B X w t := by
    apply integral_congr_ae
    filter_upwards with t
    rw [secondDeletedFullModeSum_physical]
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

end Source2414

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondNormalizedEnergy.lean; sha256: 4f4ab449662ea2821707fe9dbebc9cc60be14de3019a7a9c86c7d35a32b65db9 -/
section Source2415
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open JointLogSeparation IdealMobiusDivisorSum InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma child_ball_neg (R : ℝ) (k : Eis) :
    -k ∈ nonzeroChildFrequencyBall 1 R ↔ k ∈ nonzeroChildFrequencyBall 1 R := by
  simp only [mem_nonzeroChildFrequencyBall _ one_ne_zero,one_mul,map_neg,norm_neg]

lemma child_ball_sum_neg {β : Type*} [AddCommMonoid β] (R : ℝ) (F : Eis → β) :
    ∑ k ∈ nonzeroChildFrequencyBall 1 R,F (-k) =
      ∑ k ∈ nonzeroChildFrequencyBall 1 R,F k := by
  apply Finset.sum_bij (fun k _ => -k)
  · intro k hk
    exact (child_ball_neg R k).mpr hk
  · intro a ha b hb he
    exact neg_injective he
  · intro b hb
    exact ⟨-b,(child_ball_neg R b).mpr hb,neg_neg b⟩
  · intro k hk
    rfl

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondLabelWeight (K : ℕ) (f : Ideal Eis) : ℝ := ((idealDivisors f).card : ℝ)^(9+4*K)

theorem second_left_normalized_energy
    (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis) (γ : OuterTriple)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (Z N V : ℝ) (hZ : 0 < Z) (t : Frequency × (Fin 6 → ℝ)) :
    secondLabelEnergy K labels rows (secondModeLeft p hp hcop hg pool Ψ m z slots lists a ω (Z^N) t) γ =
      Z^(max 0 N+V) * normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
        (actualSecondInheritedPuncture m γ) slots lists a labels rows (secondLabelWeight K)
        (clippedTest ω (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
        (Z^(max 0 N)) Z (max 0 N+V) := by
  exact initial_columnEnergy_clipping_normalized p hp hcop hg pool (secondRayMinus Ψ z)
    (actualSecondInheritedPuncture m γ) slots lists a labels rows (secondLabelWeight K) ω hZ N V _

theorem second_right_normalized_energy
    (K : ℕ) (labels : Finset (Ideal Eis)) (R : ℝ) (γ : OuterTriple)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (Z N V : ℝ) (hZ : 0 < Z) (t : Frequency × (Fin 6 → ℝ)) :
    secondLabelEnergy K labels (nonzeroChildFrequencyBall 1 R)
      (secondModeRight p hp hcop hg pool Ψ m z slots lists a ω (Z^N) t) γ =
      Z^(max 0 N+V) * normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
        (actualSecondInheritedPuncture m γ) slots lists a labels (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
        (clippedTest ω (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
        (Z^(max 0 N)) Z (max 0 N+V) := by
  have he : secondLabelEnergy K labels (nonzeroChildFrequencyBall 1 R)
      (secondModeRight p hp hcop hg pool Ψ m z slots lists a ω (Z^N) t) γ =
      columnEnergy p hp hcop hg pool (secondRayPlus Ψ z) (actualSecondInheritedPuncture m γ)
        slots lists a labels (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
        (childLogTest ω ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) (Z^N) := by
    unfold secondLabelEnergy columnEnergy
    apply Finset.sum_congr rfl
    intro f hf
    simp only [secondLabelWeight,secondModeRight,secondCanonicalPolynomial]
    apply congrArg (fun a : ℝ => ((idealDivisors f).card : ℝ)^(9+4*K)*a)
    exact child_ball_sum_neg (β:=ℝ) R (fun k => ‖finiteCanonicalMarkedRow p hp hcop hg pool
      (secondRayPlus Ψ z) (actualSecondInheritedPuncture m γ) (primaryGenerator f) k
      slots lists a (childLogTest ω ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) (Z^N)‖^2)
  rw [he]
  exact initial_columnEnergy_clipping_normalized p hp hcop hg pool (secondRayPlus Ψ z)
    (actualSecondInheritedPuncture m γ) slots lists a labels (nonzeroChildFrequencyBall 1 R)
    (secondLabelWeight K) ω hZ N V _

omit [DecidableEq σ] in
theorem normalized_child_energy_radical_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X Z F : ℝ) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F =
    normalizedColumnEnergy p hp hcop hg pool Ψ
      (ConcretePrimeRowBridge.idealGenerator (Ideal.span {m}).radical)
      slots lists a labels rows D W X Z F := by
  unfold normalizedColumnEnergy
  apply Finset.sum_congr rfl
  intro f hf
  apply congrArg (fun x : ℝ => D f*x)
  apply Finset.sum_congr rfl
  intro k hk
  rw [finiteCanonicalMarkedRow_radical_puncture p hp hcop hg pool Ψ m (primaryGenerator f) k slots lists a W X]

end
end SevenEighths.InverseMoment

end OAI

end Source2415

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondDeletedPhysicalRecursive.lean; sha256: cd032a1f5ef03333090e02c4eac6bafd65856cf5b4fe423ae7647ec2962e3711 -/
section Source2416
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedPhysicalRecursiveUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_physical_recursive
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K J : ℕ) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
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
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ W₁ W₂ Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ W₁ W₂ ω₁ ω₂ Φ G E V B Y R L Z N Vlabel εchild
    U density w labels K J A hd₁ hd₂ hZ hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have he (H : ℝ) : Z^(max 0 N+Vlabel)*(A*Z^(max 0 N+Vlabel+εchild)*H) =
      (A*Z^(2*(max 0 N+Vlabel)+εchild))*H := by
    calc
      _ = A*(Z^(max 0 N+Vlabel)*Z^(max 0 N+Vlabel+εchild))*H := by ring
      _ = _ := by rw [←Real.rpow_add hZ]; congr 2; ring_nf
  apply actual_second_deleted_physical_energy p hp hcop hg hpr hinj hc source hs
    pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ W₁ W₂ ω₁ ω₂ Φ G E V B (Z^N) Y R L
    U density w labels K J (A*Z^(2*(max 0 N+Vlabel)+εchild))
    hd₁ hd₂ hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels
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

end Source2416

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondDeletedMovingEnergy.lean; sha256: bfbb54cec6144766604f98a81f2bc8d7d4e47a9db16dd920974bc0f04669b512 -/
section Source2417
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedMovingPhysicalUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
open InverseSecondProfileUniform InverseAmbientProfileTower
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
theorem actual_second_deleted_moving_physical_recursive
    (U₀ : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 6 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
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
        (ω₁ ω₂ : ℝ → ℂ) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K : ℕ) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (fun x => star (positiveSource g₁ c₁ θ₁ x)) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₁ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (positiveSource g₂ c₂ θ₂) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₂ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/(Z^N)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/(Z^N)) ≠ 0 → ∀ i,
        U₀ i ((secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B (Z^N) i)+ρ i) = 1) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
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
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  obtain ⟨C,hC,hmeasure⟩ := InverseSecondProfileUniform.second_profile_common_measure
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨C,hC,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    ω₁ ω₂ G E V B Y R L Z N Vlabel εchild ρ c₁ c₂ θ₁ θ₂ w labels K A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hRad : 0 < Y*B/(E*V^2*(Z^N)^2) := by positivity
  obtain ⟨b₃,hb₃⟩ := hmeasure (Y*B/(E*V^2*(Z^N)^2)) hRad
  obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  let g := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
  let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) hg₁
  let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) hg₂
  let den := density g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have hden : Integrable den := balanced_density_integrable g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have he := actual_second_deleted_physical_recursive p hp hcop hg hpr hinj hc source hs
    pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) ω₁ ω₂ Φ
    G E V B Y R L Z N Vlabel εchild (fun i y => U₀ i (y+ρ i)) den w labels K J A
    hd₁ hd₂ hZ hG hE hV hB hX hden (by simpa only [star_star] using hsep)
    hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have hd : (∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖den t‖) ≤
      C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+Y*B/(E*V^2*(Z^N)^2))^Aker := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact (mul_comm _ _).le.trans hMoment
  exact he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hd (by
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ))) (by positivity))

end
end SevenEighths.InverseMoment

end OAI

end Source2417

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondPunctureBudget.lean; sha256: 3d9d472342f0949e234ab4af69b5fc264ba1169428b479cd8d6e3bd616240ce9 -/
section Source2418
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_residual_norm_eq_div (E G : Finset ι) (hE : E ⊆ G) :
    primeProductNorm p (G\E) = primeProductNorm p G/primeProductNorm p E := by
  have he : primeProductNorm p G = primeProductNorm p E*primeProductNorm p (G\E) := by
    rw [←primeProductNorm_union p E (G\E) Finset.disjoint_sdiff,Finset.union_sdiff_of_subset hE]
  rw [he]
  field_simp [(primeProductNorm_pos p hp E).ne']

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_residual_norm_power_bound (E G : Finset ι) (hE : E ⊆ G)
    (Z g theta eta : ℝ) (hZ : 0 < Z)
    (hg : primeProductNorm p G ≤ Z^(g+eta))
    (hd : Z^(theta-eta) ≤ primeProductNorm p E) :
    primeProductNorm p (G\E) ≤ Z^(g-theta+2*eta) := by
  rw [second_residual_norm_eq_div p hp E G hE]
  calc
    _ ≤ Z^(g+eta)/Z^(theta-eta) := div_le_div₀ (Real.rpow_pos_of_pos hZ _).le hg
      (Real.rpow_pos_of_pos hZ _) hd
    _ = Z^((g+eta)-(theta-eta)) := (Real.rpow_sub hZ _ _).symm
    _ = _ := by congr 1; ring

include hp in

theorem actual_second_puncture_power_budget
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 0 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (hB : primeProductNorm p x.cube.support ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      Z^(Q+ell+t+g-theta+4*eta) := by
  have hr := second_residual_norm_power_bound p hp _ _ hE Z g theta eta hZ hG hD
  apply (actual_second_inherited_puncture_norm p hp hpr x hE ht u v m hm).trans
  calc
    _ ≤ (Z^Q*Z^(t+eta))*Z^(ell+eta)*Z^(g-theta+2*eta) := by
      have hb0 := (primeProductNorm_pos p hp x.cube.support).le
      have hr0 := (primeProductNorm_pos p hp (x.second.sourceCommon\x.second.divisor)).le
      gcongr
    _ = Z^((Q+(t+eta))+(ell+eta)+(g-theta+2*eta)) := by
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by congr 1; ring

end
end SevenEighths.InverseMoment

end OAI

end Source2418

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondTripleBounds.lean; sha256: af280e17b21db8efb8697ecdc2c889bc6a3adaab9781c5e5736461f405d5f6c5 -/
section Source2419
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0)

include hp in

theorem actual_second_common_center
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (Z g theta eta : ℝ) (hZ : 1 < Z)
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    -2*eta ≤ g-theta := by
  have hh : Z^(theta-eta) ≤ Z^(g+eta) :=
    hD.trans ((primeProductNorm_mono p hp hE).trans hG)
  have hh' := (Real.rpow_le_rpow_left_iff hZ).mp hh
  linarith

include hp in

theorem actual_second_label_center
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Z ell j eta : ℝ) (hZ : 1 < Z)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hJ : Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    j ≤ 2*ell+3*eta := by
  have hb := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos (Z^(ell+eta))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le h1 h2).1
  have hh := hJ.trans hb
  rw [←Real.rpow_mul_natCast (zero_lt_one.trans hZ).le] at hh
  have hh' := (Real.rpow_le_rpow_left_iff hZ).mp hh
  norm_num at hh'
  linarith

variable [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_second_q0_power_bound
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (Z ell R j eta : ℝ) (hZ : 0 < Z)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hactive : primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(R+eta))
    (hJ : Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) ≤ Z^(ell+R/2-j+5*eta/2) := by
  have hb := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos (Z^(ell+eta))
      (Real.rpow_pos_of_pos hZ _).le h1 h2).2.2
  have ha : ‖eisEmbedding (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤
      Z^((R+eta)/2) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.rpow_pos_of_pos hZ _).le).mp
    rw [←Real.rpow_mul_natCast hZ.le]
    norm_num
    simpa only [primeProductNorm,map_prod,norm_prod] using hactive
  change (Ideal.absNorm (Ideal.span {b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) : ℝ) ≤ _
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]
  apply hb.trans
  calc
    _ ≤ (Z^(ell+eta)*Z^((R+eta)/2))/Z^(j-eta) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left ha (by positivity))
        (Real.rpow_pos_of_pos hZ _) hJ
    _ = Z^((ell+eta)+(R+eta)/2-(j-eta)) := by
      rw [←Real.rpow_add hZ,←Real.rpow_sub hZ]
    _ = _ := by congr 1; ring

end
end SevenEighths.InverseMoment

end OAI

end Source2419

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondActualMass.lean; sha256: 0ad31e3f20a6f82758c322fc35288fb41a549fe7d42c7d2fbb511761634bfd86 -/
section Source2420
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic (sourceIdeal)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma nonzero_ideal_norm_one (I : Ideal Eis) (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem triple_normalized_mass_source_bounds (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Γ : Finset OuterTriple) (B T R : ℝ),
      0 < B → 0 < T → 0 < R →
      (∀ γ ∈ Γ, γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0) →
      (∀ γ ∈ Γ, (Ideal.absNorm γ.q0 : ℝ) ≤ B ∧
        (Ideal.absNorm γ.quotient : ℝ) ≤ T ∧ (Ideal.absNorm γ.residual : ℝ) ≤ R) →
      (B*T*R)⁻¹ * (∑ γ ∈ Γ, tripleDivisorWeight K γ) ≤ C*(B*T*R)^ε := by
  obtain ⟨C,hC,hb⟩ := triple_normalized_mass K ε hε
  refine ⟨C,hC,?_⟩
  intro Γ B T R hB hT hR hz hn
  rcases Γ.eq_empty_or_nonempty with he|⟨γ,hγ⟩
  · subst Γ
    simp only [Finset.sum_empty,mul_zero]
    positivity
  · obtain ⟨hq,ht,hr⟩ := hz γ hγ
    obtain ⟨hqb,htb,hrb⟩ := hn γ hγ
    exact hb Γ B T R ((nonzero_ideal_norm_one _ hq).trans hqb)
      ((nonzero_ideal_norm_one _ ht).trans htb) ((nonzero_ideal_norm_one _ hr).trans hrb) hz hn

theorem actual_second_normalized_mass (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → Eis)
      (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (u v : Eisˣ)
      (Z ell R j t g theta eta : ℝ), 0 < Z →
      (∀ x ∈ source, x.quotient ≠ 0) →
      (∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(R+eta)) →
      (∀ x ∈ source, Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x ∈ source, (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta)) →
      (∀ x ∈ source, primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta)) →
      (∀ x ∈ source, Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      Z^(-(ell+R/2-j+t+g-theta+11*eta/2)) *
        (∑ γ ∈ actualSecondTriples p u v source,tripleDivisorWeight K γ) ≤
        C*Z^((ell+R/2-j+t+g-theta+11*eta/2)*ε) := by
  obtain ⟨C,hC,hb⟩ := triple_normalized_mass_source_bounds K ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ Jo Jn source u v Z ell R j t g theta eta hZ ht hE h1 h2 ha hJ hT hG hD
  have hz : ∀ γ ∈ actualSecondTriples p u v source,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0 := by
    intro γ hγ
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    exact (actualSecondChild_nonzero p hp u v x (ht x hx)).2
  have hn : ∀ γ ∈ actualSecondTriples p u v source,
      (Ideal.absNorm γ.q0 : ℝ) ≤ Z^(ell+R/2-j+5*eta/2) ∧
      (Ideal.absNorm γ.quotient : ℝ) ≤ Z^(t+eta) ∧
      (Ideal.absNorm γ.residual : ℝ) ≤ Z^(g-theta+2*eta) := by
    intro γ hγ
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    refine ⟨actual_second_q0_power_bound p hp x u v Z ell R j eta hZ
      (h1 x hx) (h2 x hx) (ha x hx) (hJ x hx),hT x hx,?_⟩
    have hr := second_residual_norm_power_bound p hp _ _ (hE x hx) Z g theta eta hZ (hG x hx) (hD x hx)
    change (Ideal.absNorm (sourceIdeal p (x.second.sourceCommon\x.second.divisor)) : ℝ) ≤ _
    simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hr
  have hm := hb (actualSecondTriples p u v source)
    (Z^(ell+R/2-j+5*eta/2)) (Z^(t+eta)) (Z^(g-theta+2*eta))
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hz hn
  have he : Z^(ell+R/2-j+5*eta/2)*Z^(t+eta)*Z^(g-theta+2*eta) =
      Z^(ell+R/2-j+t+g-theta+11*eta/2) := by
    rw [←Real.rpow_add hZ,←Real.rpow_add hZ]
    congr 1
    ring
  rw [he,←Real.rpow_mul hZ.le,←Real.rpow_neg hZ.le] at hm
  exact hm

end
end SevenEighths.InverseMoment

end OAI

end Source2420

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondOriginalMass.lean; sha256: 38e65e0dfbb7674c510b290d692efa4d65f271ac65cd96e2ebfa8b237ee27941 -/
section Source2421
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic (sourceIdeal)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem actual_second_original_mass (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → Eis)
      (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (u v : Eisˣ)
      (Z ell R j t g theta eta : ℝ), 0 < Z →
      (∀ x ∈ source, x.quotient ≠ 0) →
      (∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(R+eta)) →
      (∀ x ∈ source, Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x ∈ source, (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta)) →
      (∀ x ∈ source, primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta)) →
      (∀ x ∈ source, Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      (∑ γ ∈ actualSecondTriples p u v source,tripleDivisorWeight K γ) ≤
        C*Z^((ell+R/2-j+t+g-theta+11*eta/2)*(1+ε)) := by
  obtain ⟨C,hC,hb⟩ := actual_second_normalized_mass K ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ Jo Jn source u v Z ell R j t g theta eta hZ ht hE h1 h2 ha hJ hT hG hD
  have hm := hb p hp source u v Z ell R j t g theta eta hZ ht hE h1 h2 ha hJ hT hG hD
  let c := ell+R/2-j+t+g-theta+11*eta/2
  calc
    _ = Z^c * (Z^(-c)*(∑ γ∈actualSecondTriples p u v source,tripleDivisorWeight K γ)) := by
      rw [←mul_assoc,←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero,one_mul]
    _ ≤ Z^c*(C*Z^(c*ε)) := mul_le_mul_of_nonneg_left hm (Real.rpow_pos_of_pos hZ _).le
    _ = _ := by
      rw [mul_left_comm,←Real.rpow_add hZ]
      congr 2
      dsimp only [c]
      ring

end
end SevenEighths.InverseMoment

end OAI

end Source2421

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondDeletedMovingMass.lean; sha256: 508ad97d3a86a9738bf5064950ad52992aaca9da3458691758d73c049293328b -/
section Source2422
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedMovingMassUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
open InverseSecondProfileUniform InverseAmbientProfileTower
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_second_deleted_moving_mass_recursive
    (U₀ : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 6 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J K : ℕ) (εmass : ℝ) (hεmass : 0 < εmass) :
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
        (ω₁ ω₂ : ℝ → ℂ) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (fun x => star (positiveSource g₁ c₁ θ₁ x)) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₁ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (positiveSource g₂ c₂ θ₂) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₂ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/(Z^N)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/(Z^N)) ≠ 0 → ∀ i,
        U₀ i ((secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B (Z^N) i)+ρ i) = 1) →
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
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  obtain ⟨Cp,hCp,hmoving⟩ := actual_second_deleted_moving_physical_recursive (ι:=ι) (σ:=σ)
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  obtain ⟨Cm,hCm,hmass⟩ := actual_second_original_mass K εmass hεmass
  refine ⟨Cp*Cm,mul_nonneg hCp hCm.le,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    ω₁ ω₂ G E V B Y R L Z N Vlabel εchild ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have he := hmoving p hp hcop hg hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ ω₁ ω₂ G E V B Y R L Z N Vlabel εchild
    ρ c₁ c₂ θ₁ θ₂ w labels K A hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hm := hmass p hp source 1 1 Z ell Ractive j tcount gcount theta eta hZ
    hs.quotient_nonzero hs.second_divisor hcube₁ hcube₂ hactive hj hquot hcommon hdiv
  have hfac : 0 ≤ 36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild)) := by positivity
  have hh : 0 ≤ Cp*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
        (1+Y*B/(E*V^2*(Z^N)^2))^Aker := by positivity
  have hpref : 0 ≤ Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N):ℝ):ℂ)⁻¹‖ := by positivity
  have hb := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hfac) hh) hpref
  exact he.trans (hb.trans_eq (by ring))

end
end SevenEighths.InverseMoment

end OAI

end Source2422

/- Original source: OAI/NumberTheory/DirichletL/Inversion/SecondChildWindows.lean; sha256: f6d1f11760555630b2a8f19b0b9821a1845d94f6d9f266aef9923b5cf0825a13 -/
section Source2423
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseSecondChildWindows
open InverseMoment InverseSecondProfileUniform
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
local notation "O" => ActualEisensteinCubic.O

theorem positive_cutoff (a b : ℝ) (ha : 0<a) (_hab : a≤b) :
    ∃ w : 𝓢(ℝ,ℂ), HasCompactSupport (w : ℝ→ℂ) ∧
      (∀ x∈Set.Icc a b,w x=1) ∧ tsupport (w : ℝ→ℂ)⊆Set.Icc (a/2) (b+1) := by
  have hKU : Set.Icc a b⊆Set.Ioo (a/2) (b+1) := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hKU
  let v : ℝ→ℂ := fun x => (f x:ℂ)
  have hv : ContDiff ℝ ∞ v := Complex.ofRealCLM.contDiff.comp (by simpa using hf)
  have hvs : Function.support v⊆Set.Icc (a/2) (b+1) := by
    intro x hx
    have hh : x∈Function.support f := by simpa [v,Function.mem_support] using hx
    rw [hs] at hh
    exact ⟨hh.1.le,hh.2.le⟩
  have hvc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hvs
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,closure_minimal hvs isClosed_Icc⟩
  intro x hx
  change (f x:ℂ)=1
  rw [(hone x).mp hx]
  rfl

theorem positiveSource_log_bound (g : 𝓢(ℝ,ℂ)) (m bcap c θ x : ℝ)
    (_hm : 0≤m) (hs : Function.support g⊆Set.Icc (-m) m)
    (hc : 1≤c) (hcb : c≤bcap) (_hx : 0<x)
    (hn : positiveSource g c θ x≠0) : |Real.log x|≤m+Real.log bcap := by
  have hc0 : 0<c := zero_lt_one.trans_le hc
  have hgn : g (Real.log x+Real.log c)≠0 := (mul_ne_zero_iff.mp hn).2
  have hh := hs hgn
  have hcl : 0≤Real.log c := Real.log_nonneg hc
  have hclb : Real.log c≤Real.log bcap := Real.log_le_log hc0 hcb
  rw [abs_le]
  constructor <;> linarith [hh.1,hh.2]

theorem positiveSource_ratio_support (g : 𝓢(ℝ,ℂ)) (m bcap c θ x : ℝ)
    (hm : 0≤m) (hs : Function.support g⊆Set.Icc (-m) m)
    (hc : 1≤c) (hcb : c≤bcap) (hx : 0<x)
    (hn : positiveSource g c θ x≠0) :
    x∈Set.Icc (Real.exp (-(m+Real.log bcap))) (Real.exp (m+Real.log bcap)) := by
  have hh := (abs_le.mp (positiveSource_log_bound g m bcap c θ x hm hs hc hcb hx hn))
  exact ⟨(Real.le_log_iff_exp_le hx).mp hh.1,(Real.log_le_iff_le_exp hx).mp hh.2⟩

theorem translated_log_bound (a b x ρ B : ℝ) (ha : 0<a)
    (hx : x∈Set.Icc a b) (hρ : |ρ|≤B) :
    |Real.log x+ρ|≤|Real.log a|+|Real.log b|+B := by
  have hx0 := ha.trans_le hx.1
  have hlo := Real.log_le_log ha hx.1
  have hhi := Real.log_le_log hx0 hx.2
  have hl : |Real.log x|≤|Real.log a|+|Real.log b| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
    · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]
  exact (abs_add_le _ _).trans (add_le_add hl hρ)

def outerIndex (i : Fin 4) : Fin 6 := i.castLE (by decide)

theorem fixed_windows (m bcap : ℝ) (lo hi : Fin 4→ℝ) (Bρ : Fin 6→ℝ)
    (hm : 0≤m) (_hcap : 1≤bcap) (hlo : ∀ i,0<lo i)
    (hhi : ∀ i,lo i≤hi i) (hBρ : ∀ i,0≤Bρ i) :
    ∃ (w : 𝓢(ℝ,ℂ)) (U : Fin 6→𝓢(ℝ,ℂ)) (M : Fin 6→ℝ) (a b : ℝ),
      0<a ∧ a≤b ∧ HasCompactSupport (w : ℝ→ℂ) ∧
      tsupport (w : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀ i,0≤M i) ∧ (∀ i,HasCompactSupport (U i : ℝ→ℂ)) ∧
      (∀ i,Function.support (U i)⊆Set.Icc (-M i) (M i)) ∧
      (∀ (g : 𝓢(ℝ,ℂ)),Function.support g⊆Set.Icc (-m) m →
        ∀ (c θ u v n : ℝ),1≤c → c≤bcap →
        u∈Set.Icc (lo 0) (hi 0) → v∈Set.Icc (lo 2) (hi 2) → 0<n →
        positiveSource g c θ (u*v*n)≠0 → w n=1) ∧
      (∀ (q : Fin 6→ℝ) (ρ : Fin 6→ℝ),
        (∀ i,|ρ i|≤Bρ i) →
        (∀ i : Fin 4,q (outerIndex i)∈Set.Icc (lo i) (hi i)) →
        w (q 4)≠0 → w (q 5)≠0 → ∀ i,U i (Real.log (q i)+ρ i)=1) := by
  let R := m+Real.log bcap
  let a := Real.exp (-R)/(hi 0*hi 2)
  let b := Real.exp R/(lo 0*lo 2)
  have hhi0 (i : Fin 4) : 0<hi i := (hlo i).trans_le (hhi i)
  have ha : 0<a := div_pos (Real.exp_pos _) (mul_pos (hhi0 0) (hhi0 2))
  have hb : 0<b := div_pos (Real.exp_pos _) (mul_pos (hlo 0) (hlo 2))
  obtain ⟨w,hwc,hwone,hws⟩ := positive_cutoff a (a+b+1) ha (by linarith)
  let l : Fin 6→ℝ := ![lo 0,lo 1,lo 2,lo 3,a/2,a/2]
  let u : Fin 6→ℝ := ![hi 0,hi 1,hi 2,hi 3,(a+b+1)+1,(a+b+1)+1]
  have hl (i : Fin 6) : 0<l i := by
    fin_cases i
    · exact hlo 0
    · exact hlo 1
    · exact hlo 2
    · exact hlo 3
    · exact half_pos ha
    · exact half_pos ha
  let H (i : Fin 6) := |Real.log (l i)|+|Real.log (u i)|+Bρ i
  have hH (i : Fin 6) : 0≤H i := add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hBρ i)
  choose V hVc hVs hVone hVsupport hVzero using
    fun i : Fin 6 => FourierBridge.exists_complex_smooth_cutoff (H i) (hH i)
  let U (i : Fin 6) : 𝓢(ℝ,ℂ) := (hVc i).toSchwartzMap (hVs i)
  refine ⟨w,U,(fun i=>H i+1),a/2,(a+b+1)+1,half_pos ha,by linarith,hwc,hws,
    (fun i=>by linarith [hH i]),hVc,(fun i=>(subset_tsupport _).trans (hVsupport i)),?_,?_⟩
  · intro g hg c θ u v n hc hcb hu hv hn hnz
    have hu0 := (hlo 0).trans_le hu.1
    have hv0 := (hlo 2).trans_le hv.1
    have hs := positiveSource_ratio_support g m bcap c θ (u*v*n) hm hg hc hcb
      (mul_pos (mul_pos hu0 hv0) hn) hnz
    have hnlo : a≤n := by
      apply (div_le_iff₀ (mul_pos (hhi0 0) (hhi0 2))).mpr
      calc
        _ ≤ u*v*n := hs.1
        _ ≤ (hi 0*hi 2)*n := mul_le_mul_of_nonneg_right
          (mul_le_mul hu.2 hv.2 hv0.le (hhi0 0).le) hn.le
        _ = _ := by ring
    have hnhi : n≤b := by
      apply (le_div_iff₀ (mul_pos (hlo 0) (hlo 2))).mpr
      calc
        _ = (lo 0*lo 2)*n := by ring
        _ ≤ u*v*n := mul_le_mul_of_nonneg_right
          (mul_le_mul hu.1 hv.1 (hlo 2).le hu0.le) hn.le
        _ ≤ _ := hs.2
    exact hwone n ⟨hnlo,by linarith⟩
  · intro q ρ hρ hblock hleft hright i
    have hq (k : Fin 6) : q k∈Set.Icc (l k) (u k) := by
      fin_cases k
      · exact hblock 0
      · exact hblock 1
      · exact hblock 2
      · exact hblock 3
      · exact hws (subset_tsupport _ hleft)
      · exact hws (subset_tsupport _ hright)
    exact hVone i _ (translated_log_bound (l i) (u i) (q i) (ρ i) (Bρ i) (hl i) (hq i) (hρ i))

def actualOuterRatios {ι : Type*} [DecidableEq ι] (p : ι→O)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (G E V B : ℝ) : Fin 4→ℝ :=
  ![primeProductNorm p x.second.sourceCommon/G,
    ‖ConcreteTraceCRT.eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.second.divisor)‖^2/E,
    primeProductNorm p x.second.overlap/V,‖ConcreteTraceCRT.eisEmbedding x.second.frequency‖^2/B]

lemma actualRelativeNorm_outer {ι : Type*} [DecidableEq ι] (p : ι→O)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex)
    (Q₁ Q₂ : Finset ι) (G E V B X : ℝ) (i : Fin 4) :
    secondRelativeNorm (secondActualNorms p (secondInheritedProfile p x Ψ m z) Q₁ Q₂)
      G E V B X (outerIndex i)=actualOuterRatios p x G E V B i := by
  fin_cases i <;> rfl

theorem actual_second_child_windows (g₁ g₂ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 4→ℝ) (Bρ : Fin 6→ℝ)
    (hm₁ : 0≤m₁) (_hm₂ : 0≤m₂) (hcap : 1≤bcap)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂)
    (hlo : ∀ i,0<lo i) (hhi : ∀ i,lo i≤hi i) (hBρ : ∀ i,0≤Bρ i) :
    ∃ (w₁ w₂ : 𝓢(ℝ,ℂ)) (U₀ : Fin 6→𝓢(ℝ,ℂ)) (M₀ : Fin 6→ℝ) (a b : ℝ),
      0<a ∧ a≤b ∧ HasCompactSupport (w₁ : ℝ→ℂ) ∧ HasCompactSupport (w₂ : ℝ→ℂ) ∧
      tsupport (w₁ : ℝ→ℂ)⊆Set.Icc a b ∧ tsupport (w₂ : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀ i,0≤M₀ i) ∧ (∀ i,HasCompactSupport (U₀ i : ℝ→ℂ)) ∧
      (∀ i,Function.support (U₀ i)⊆Set.Icc (-M₀ i) (M₀ i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (_hp : ∀ i,p i≠0)
      [∀ i,(Ideal.span {p i}).IsMaximal]
      {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (pool : Finset ι)
      (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex) (G E V B X : ℝ)
      (ρ : Fin 6→ℝ) (c₁ c₂ θ₁ θ₂ : ℝ),
      0<G → 0<E → 0<V → 0<B → 0<X →
      (∀ i,|ρ i|≤Bρ i) → 1≤c₁ → c₁≤bcap → 1≤c₂ → c₂≤bcap →
      (∀ x∈source,∀ i,actualOuterRatios p x G E V B i∈Set.Icc (lo i) (hi i)) →
      (∀ x∈source,∀ Q∈(pool\x.second.overlap).powerset,
        star (positiveSource g₁ c₁ θ₁
          (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*primeProductNorm p Q/(G*V*X)))≠0 →
        w₁ (primeProductNorm p Q/X)=1) ∧
      (∀ x∈source,∀ Q∈(pool\x.second.overlap).powerset,
        positiveSource g₂ c₂ θ₂
          (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*primeProductNorm p Q/(G*V*X))≠0 →
        w₂ (primeProductNorm p Q/X)=1) ∧
      (∀ j∈secondProfileIndices source pool (fun x=>secondInheritedProfile p x Ψ m z),
        w₁ (primeProductNorm p j.2.1/X)≠0 → w₂ (primeProductNorm p j.2.2/X)≠0 → ∀ i,
        U₀ i (secondRelativeLog
          (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2) G E V B X i+ρ i)=1) := by
  let mmax := max m₁ m₂
  have hmmax : 0≤mmax := hm₁.trans (le_max_left _ _)
  have hg₁' : Function.support g₁⊆Set.Icc (-mmax) mmax := by
    intro x hx
    have h := hg₁ hx
    exact ⟨(neg_le_neg (le_max_left _ _)).trans h.1,h.2.trans (le_max_left _ _)⟩
  have hg₂' : Function.support g₂⊆Set.Icc (-mmax) mmax := by
    intro x hx
    have h := hg₂ hx
    exact ⟨(neg_le_neg (le_max_right _ _)).trans h.1,h.2.trans (le_max_right _ _)⟩
  obtain ⟨w,U,M,a,b,ha,hab,hwc,hws,hM,hUc,hUs,hfresh,hcut⟩ :=
    fixed_windows mmax bcap lo hi Bρ hmmax hcap hlo hhi hBρ
  refine ⟨w,w,U,M,a,b,ha,hab,hwc,hwc,hws,hws,hM,hUc,hUs,?_⟩
  intro ι _ p hp _ Jo Jn source pool Ψ m z G E V B X ρ c₁ c₂ θ₁ θ₂ hG hE hV hB hX hρ hc₁ hcb₁ hc₂ hcb₂ hblock
  have he (x : MarkedSecondSource ι Jo Jn) (Q : Finset ι) :
      (primeProductNorm p x.second.sourceCommon/G)*(primeProductNorm p x.second.overlap/V)*(primeProductNorm p Q/X)=
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*primeProductNorm p Q/(G*V*X) := by
    field_simp
  refine ⟨?_,?_,?_⟩
  · intro x hx Q _ hn
    apply hfresh g₁ hg₁' c₁ θ₁ _ _ _ hc₁ hcb₁ (hblock x hx 0) (hblock x hx 2)
      (div_pos (primeProductNorm_pos p hp Q) hX)
    change positiveSource g₁ c₁ θ₁ ((primeProductNorm p x.second.sourceCommon/G)*
      (primeProductNorm p x.second.overlap/V)*(primeProductNorm p Q/X))≠0
    rw [he]
    exact star_ne_zero.mp hn
  · intro x hx Q _ hn
    apply hfresh g₂ hg₂' c₂ θ₂ _ _ _ hc₂ hcb₂ (hblock x hx 0) (hblock x hx 2)
      (div_pos (primeProductNorm_pos p hp Q) hX)
    change positiveSource g₂ c₂ θ₂ ((primeProductNorm p x.second.sourceCommon/G)*
      (primeProductNorm p x.second.overlap/V)*(primeProductNorm p Q/X))≠0
    rw [he]
    exact hn
  · intro j hj hleft hright i
    apply hcut (secondRelativeNorm
      (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2) G E V B X) ρ hρ
      (fun k=>?_) hleft hright i
    rw [actualRelativeNorm_outer]
    exact hblock j.1 ((mem_secondProfileIndices source pool _ j).mp hj).1 k

end SevenEighths.InverseSecondChildWindows

end

end OAI

end Source2423

/- Original source: OAI/NumberTheory/DirichletL/Descent/ClippedFourier.lean; sha256: 99a6e67307379b73ad399bd3dd3e18a480eb5f8c6b95495522feff05dd2f0006 -/
section Source2424
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns InverseInitialOverlapFourier SecondPassIntegration JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

theorem clipped_fixed_window (W:ℝ→ℂ) (lo hi b:ℝ) (hlo:0<lo) (hb:1≤b)
    (hW:Function.support W⊆Set.Icc lo hi):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀c,1≤c→c≤b→∀y,0<y→wFresh y*W (c*y)=W (c*y):=by
  have hb0:0<b:=zero_lt_one.trans_le hb
  let a:=lo/b
  let B:=a+|hi|+1
  have ha:0<a:=div_pos hlo hb0
  obtain ⟨wFresh,hc,hone,hs⟩:=InverseSecondChildWindows.positive_cutoff a B ha (by dsimp [B];linarith [abs_nonneg hi])
  refine ⟨wFresh,a/2,B+1,half_pos ha,by dsimp [B];linarith [abs_nonneg hi],hc,hs,?_⟩
  intro c hc hcb y hy
  by_cases hz:W (c*y)=0
  · simp only [hz,mul_zero]
  have hw:=hW hz
  have hay:a≤y:=by
    apply (div_le_iff₀ hb0).mpr
    calc
      lo≤c*y:=hw.1
      _≤y*b:=by nlinarith
  have hyhi:y≤hi:=le_trans (by nlinarith) hw.2
  have hyB:y≤B:=by dsimp [B];linarith [le_abs_self hi]
  rw [hone y ⟨hay,hyB⟩,one_mul]

theorem clipped_test_fourier (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (wFresh:ℝ→ℂ)(c θ y:ℝ)(hc:0<c)(hy:0<y)(hwFresh:wFresh y*W (c*y)=W (c*y)):
    clippedTest W c θ y =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t *
        childLogTest wFresh (θ+t) y:=by
  let g:=CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  change clippedTest W c θ y=∫t:ℝ,density g (Real.log c) t*childLogTest wFresh (θ+t) y
  have he (t:ℝ):density g (Real.log c) t*childLogTest wFresh (θ+t) y=
      ((𝓕 g) t*logPhase t (Real.log c+Real.log y))*(wFresh y*logPhase θ (Real.log y)):=by
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  simp_rw [he]
  rw [integral_mul_const]
  have hi':(∫t:ℝ,(𝓕 g) t*logPhase t (Real.log c+Real.log y))=W (c*y):=by
    calc
      _=(∫t:ℝ,logPhase t (Real.log c+Real.log y)*(𝓕 g) t):=by
        apply integral_congr_ae
        filter_upwards with t
        ring
      _=g (Real.log c+Real.log y):=(schwartz_logPhase_inversion g _).symm
      _= _:=by
        simp only [g,CubicReflectionKernel.logSchwartz_apply,Real.exp_add,Real.exp_log hc,Real.exp_log hy]
  rw [hi']
  unfold clippedTest childLogTest
  calc
    W (c*y)*logPhase θ (Real.log y)=(wFresh y*W (c*y))*logPhase θ (Real.log y):=by rw [hwFresh]
    _= _:=by ring

variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_clipped_mode_integrable
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(m f k:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (g:𝓢(ℝ,ℂ))(wFresh:ℝ→ℂ)(c θ X:ℝ):
    Integrable (fun t:ℝ=>density g (Real.log c) t*
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a (childLogTest wFresh (θ+t)) X):=by
  simp_rw [finiteCanonicalMarkedRow_actual_columns p hp hcop hg hpr]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro U hU
  convert fourier_phase_integrable g (Real.log c+Real.log (primeProductNorm p U/X))
    (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
      primeMark slots lists a U*wFresh (primeProductNorm p U/X)*logPhase θ (Real.log (primeProductNorm p U/X))) using 1
  funext t
  simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
  ring

theorem canonical_clipped_fourier
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(m f k:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:ℝ→ℂ)(lo hi:ℝ)(hlo:0<lo)(hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (wFresh:ℝ→ℂ)(c θ X:ℝ)(hc:0<c)(hX:0<X)(hwFresh:∀y,0<y→wFresh y*W (c*y)=W (c*y)):
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a (clippedTest W c θ) X=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t *
        finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a (childLogTest wFresh (θ+t)) X:=by
  simp_rw [finiteCanonicalMarkedRow_actual_columns p hp hcop hg hpr]
  simp only [Finset.mul_sum]
  have hints (U:Finset ι):Integrable (fun t:ℝ=>
      density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t*
      (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
        (primeMark slots lists a U*childLogTest wFresh (θ+t) (primeProductNorm p U/X)))):=by
    convert fourier_phase_integrable (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)
      (Real.log c+Real.log (primeProductNorm p U/X))
      (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
        primeMark slots lists a U*wFresh (primeProductNorm p U/X)*logPhase θ (Real.log (primeProductNorm p U/X))) using 1
    funext t
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  rw [integral_finsetSum _ (fun U _=>hints U)]
  apply Finset.sum_congr rfl
  intro U hU
  rw [clipped_test_fourier W lo hi hlo hs hW wFresh c θ _ hc
    (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp U) hX) (hwFresh _ (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp U) hX))]
  rw [←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring

end SevenEighths.InverseMoment

end

end OAI

end Source2424

/- Original source: OAI/NumberTheory/DirichletL/Descent/ClippedEnergy.lean; sha256: 356474327f3fe191325d71907d97eb5eff25e2592a13d85257cde62342f8f30a -/
section Source2425
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns InverseInitialOverlapFourier CompletedGauss
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem normalized_energy_vector
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(hD:∀f∈labels,0≤D f)
    (W:ℝ→ℂ)(X Z F:ℝ):
    (∑v:labels×rows,‖(Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a W X‖^2)=
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F:=by
  unfold normalizedColumnEnergy
  rw [Fintype.sum_prod_type,←Finset.sum_coe_sort labels]
  apply Finset.sum_congr rfl
  intro f hf
  rw [←Finset.sum_coe_sort rows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_assoc,norm_mul,mul_pow,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hD f f.property)]

theorem canonical_clipped_energy
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(hD:∀f∈labels,0≤D f)
    (W:ℝ→ℂ)(lo hi:ℝ)(hlo:0<lo)(hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (wFresh:ℝ→ℂ)(c θ X Z F E:ℝ)(J:ℕ)(hc:0<c)(hX:0<X)(hE:0≤E)
    (hw:∀y,0<y→wFresh y*W (c*y)=W (c*y))
    (he:∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest wFresh s) X Z F≤E*(1+‖s‖)^(2*J)):
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (clippedTest W c θ) X Z F≤
      E*(1+‖θ‖)^(2*J)*(∫t:ℝ,(1+‖t‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) t‖)^2:=by
  let g:=CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  let b:=density g (Real.log c)
  let phi:labels×rows→ℝ→ℂ:=fun v t=>(Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a
      (childLogTest wFresh (θ+t)) X
  have hint(v:labels×rows):Integrable (fun t:ℝ=>b t*phi v t):=by
    convert (canonical_clipped_mode_integrable p hp hcop hg hpr pool Ψ m (primaryGenerator v.1) v.2
      slots lists a g wFresh c θ X).const_mul ((Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)) using 1
    funext t
    dsimp [b,phi]
    ring
  have hbound(t:ℝ):(∑v:labels×rows,‖phi v t‖^2)≤
      (E*(1+‖θ‖)^(2*J))*((1+‖t‖)^J)^2:=by
    dsimp only [phi]
    rw [normalized_energy_vector p hp hcop hg pool Ψ m slots lists a labels rows D hD]
    apply (he (θ+t)).trans
    have hb:1+‖θ+t‖≤(1+‖θ‖)*(1+‖t‖):=by
      have hh:=norm_add_le θ t
      nlinarith [mul_nonneg (norm_nonneg θ) (norm_nonneg t)]
    calc
      _≤E*((1+‖θ‖)*(1+‖t‖))^(2*J):=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) hE
      _= _:=by rw [mul_pow,pow_mul];ring
  have hden:Integrable (fun t:ℝ=>(1+‖t‖)^J*‖b t‖):=by
    simpa only [b,density_norm] using AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hh:=CenteredMomentHeckeWindowEnergy.finite_weighted_integral_energy b phi
    (fun t:ℝ=>(1+‖t‖)^J) (by intro t;positivity)
    (E*(1+‖θ‖)^(2*J)) (by positivity) hden hint hbound
  have heq(v:labels×rows): (∫t:ℝ,b t*phi v t)=
      (Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a
        (clippedTest W c θ) X:=by
    rw [canonical_clipped_fourier p hp hcop hg hpr pool Ψ m (primaryGenerator v.1) v.2
      slots lists a W lo hi hlo hs hW wFresh c θ X hc hX hw,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [b,phi,g]
    ring
  simp_rw [heq] at hh
  rw [normalized_energy_vector p hp hcop hg pool Ψ m slots lists a labels rows D hD] at hh
  simpa only [b,density_norm,g] using hh

end SevenEighths.InverseMoment

end

end OAI

end Source2425

/- Original source: OAI/NumberTheory/DirichletL/Descent/ClippedUniform.lean; sha256: d6914ab37c5d60fedb3082ce5a3fbde91d4c035b52e18e74ba70bf83471645f7 -/
section Source2426
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem canonical_clipped_uniform
    (W:ℝ→ℂ)(lo hi b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀J:ℕ,∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(_hD:∀f∈labels,0≤D f)
      (c θ X Z F E:ℝ),1≤c→c≤b→0<X→0≤E→
      (∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) X Z F≤E*(1+‖s‖)^(2*J))→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (clippedTest W c θ) X Z F≤C*E*(1+‖θ‖)^(2*J):=by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,hagree⟩:=clipped_fixed_window W lo hi b hlo hb hs
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  let M:=(∫t:ℝ,(1+‖t‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) t‖)^2
  refine ⟨M+1,by dsimp [M];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD c θ X Z F E hc1 hcb hX hE he
  have hh:=canonical_clipped_energy p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
    W lo hi hlo hs hW wFresh c θ X Z F E J (zero_lt_one.trans_le hc1) hX hE
    (hagree c hc1 hcb) he
  apply hh.trans
  change E*(1+‖θ‖)^(2*J)*M≤(M+1)*E*(1+‖θ‖)^(2*J)
  have hn:0≤E*(1+‖θ‖)^(2*J):=by positivity
  nlinarith

end SevenEighths.InverseMoment

end

end OAI

end Source2426

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerUniform.lean; sha256: 33775725dd6bbcb12eeb630415b83bf6a6976a3de31fb281508affebd20a5ef1 -/
section Source2427
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic CompletedGauss
namespace SevenEighths.InverseInitialEnergyCallerUniform
open InverseMoment InverseInitialClippedColumns InverseInitialProfile
local notation "Eis"=>ActualEisensteinCubic.O

theorem initial_height_bound (J:ℕ)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
    (h:ℝ)(hh:h = -leftHeight z ∨ h=rightHeight z) :
    (1+‖h‖)^(2*J)≤tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2 := by
  have hb := child_height_moment_bound (2*J) z
  have hl : 1≤(1+‖leftHeight z‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg (leftHeight z)])
  have hr : 1≤(1+‖rightHeight z‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg (rightHeight z)])
  rw [show 2*(2*J)=4*J by omega] at hb
  rcases hh with rfl|rfl
  · rw [norm_neg]
    exact (le_mul_of_one_le_right (by positivity) hr).trans hb
  · exact (le_mul_of_one_le_left (by positivity) hl).trans hb

theorem initial_raw_uniform
    (W:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hs:Function.support W⊆Set.Icc lo b)(hW:ContDiff ℝ ∞ W):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀J:ℕ,∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(m:Eis)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)(D:Ideal Eis→ℝ)(_hD:∀f∈labels,0≤D f)
      (Z N F E:ℝ)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))(h:ℝ),1<Z→0≤E→
      (h = -leftHeight z ∨ h=rightHeight z)→
      (∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) (Z^(max 0 N)) Z F≤E*(1+‖s‖)^(2*J))→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest W h) (Z^N) Z F≤C*E*(tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) := by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,huniform⟩ := canonical_clipped_uniform W lo b b hlo hb hs hW
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  obtain ⟨C,hC,hbound⟩ := huniform J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD Z N F E z h hZ hE hh hm
  by_cases hne:(freshColumns p pool W (Z^N)).Nonempty
  · obtain ⟨hc1,hcb⟩ := freshColumns_clipping_range p hp pool W lo b Z N hZ hb hs hne
    rw [InverseInitialEnergyCallerClipping.normalized_energy_clipping p hp hcop hg
      pool Ψ m slots lists a labels rows D W (by linarith) N h F]
    apply (hbound p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
      (Z^(max 0 N-N)) h (Z^(max 0 N)) Z F E hc1 hcb (by positivity) hE hm).trans
    exact mul_le_mul_of_nonneg_left (initial_height_bound J z h hh) (mul_nonneg hC.le hE)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    unfold normalizedColumnEnergy
    simp_rw [canonical_row_zero_of_freshColumns_empty p hp hcop hg pool Ψ m _ _
      slots lists a W (Z^N) h he,mul_zero,norm_zero,zero_pow (by omega : (2:ℕ)≠0),
      Finset.sum_const_zero,mul_zero,Finset.sum_const_zero]
    dsimp [tripleHeight,coordinateHeight]
    positivity

end SevenEighths.InverseInitialEnergyCallerUniform

end

end OAI

end Source2427

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerReference.lean; sha256: 9b82332462920a68b36328a82c3ab40624705a9fc8236e09b632ae3d5aa511a3 -/
section Source2428
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerReference
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerBranch
local notation "Eis"=>ActualEisensteinCubic.O
local instance initialEnergyUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem actual_physical_reference_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (Φ:𝓢(ℝ,ℂ))(V:Fin 6→ℝ→ℂ)(M:Fin 6→ℝ)
    (hV:∀i,ContDiff ℝ ∞ (V i))(hS:∀i,HasCompactSupport (V i))
    (hM:∀i,0≤M i)(hbox:∀i y,V i y≠0→|y|≤M i)
    (ω₁ ω₂:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hω₁:Function.support ω₁⊆Set.Icc lo b)(hω₂:Function.support ω₂⊆Set.Icc lo b)
    (hd₁:ContDiff ℝ ∞ ω₁)(hd₂:ContDiff ℝ ∞ ω₂) :
    ∃(fresh₁ fresh₂:𝓢(ℝ,ℂ)),
      (∃af bf:ℝ,0<af ∧ af≤bf ∧ HasCompactSupport (fresh₁:ℝ→ℂ) ∧
        tsupport (fresh₁:ℝ→ℂ)⊆Set.Icc af bf) ∧
      (∃af bf:ℝ,0<af ∧ af≤bf ∧ HasCompactSupport (fresh₂:ℝ→ℂ) ∧
        tsupport (fresh₂:ℝ→ℂ)⊆Set.Icc af bf) ∧
    ∀(J N:ℕ)(U π:ℝ),0≤U→0<π→∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)(_hf:∀x∈S,x.frequency≠0)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (Z D B v θ H R m η:ℝ)(_hZ:1<Z)(_hR:R≤U)
      (_hη:0≤η*Real.log Z)(c₁ c₂ θ₁ θ₂:ℝ)(_hc₁:0<c₁)(_hc₂:0<c₂)
      (_hsupport:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F A ε:ℝ)(_hA:0≤A)
      (_hδ:max 0 (columnCenter D B v)-columnCenter D B v≤3*η)
      (_hF:F=D-B+θ+(max 0 (columnCenter D B v)-columnCenter D B v))
      (_hReq:R=B-θ+2*η)
      (_hmoment:∀s:ℝ,∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest fresh₁ s)
          (Z^(max 0 (columnCenter D B v))) Z F≤(A*Z^(F+ε))*(1+‖s‖)^(2*J) ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest fresh₂ s)
          (Z^(max 0 (columnCenter D B v))) Z F≤(A*Z^(F+ε))*(1+‖s‖)^(2*J)),
      ‖physicalBlock p hp hcop hg (pointSource pool S) (w ∘ erasePoint) Ψ j
        (primeMark slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+11*η+π+ε)*A*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)) := by
  obtain ⟨fresh₁,af₁,bf₁,haf₁,hab₁,hc₁,hsf₁,hu₁⟩ :=
    InverseInitialEnergyCallerUniform.initial_raw_uniform ω₁ lo b hlo hb hω₁ hd₁
  obtain ⟨fresh₂,af₂,bf₂,haf₂,hab₂,hc₂,hsf₂,hu₂⟩ :=
    InverseInitialEnergyCallerUniform.initial_raw_uniform ω₂ lo b hlo hb hω₂ hd₂
  refine ⟨fresh₁,fresh₂,⟨af₁,bf₁,haf₁,hab₁,hc₁,hsf₁⟩,⟨af₂,bf₂,haf₂,hab₂,hc₂,hsf₂⟩,?_⟩
  intro J N U π hU hπ
  obtain ⟨C₁,hC₁,hh₁⟩ := hu₁ J
  obtain ⟨C₂,hC₂,hh₂⟩ := hu₂ J
  obtain ⟨Cp,hCp,hphysical⟩ := InverseInitialEnergyCallerPhysical.actual_physical_block_bound
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox (4*J) N U π hU hπ
  refine ⟨Cp*(C₁+C₂),mul_pos hCp (add_pos hC₁ hC₂),?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha
    Z D B v θ H R m η hZ hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F A ε hA hδ hF hReq hmoment
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hm : ∀z:JointLogSeparation.Frequency×(Fin 6→ℝ),∀ρ:SecondRayIndex,
      ∀J₁∈slots.powerset,∀J₂∈slots.powerset,∀t∈quotientSet p S,
      normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
        (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
        (Z^(columnCenter D B v)) Z F≤((C₁+C₂)*(A*Z^(F+ε)))*
          (tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) ∧
      normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
        (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
        (Z^(columnCenter D B v)) Z F≤((C₁+C₂)*(A*Z^(F+ε)))*
          (tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) := by
    intro z ρ J₁ hJ₁ J₂ hJ₂ t ht
    have hb₁ := hh₁ p hp hcop hg hpr pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
      (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
      (by intros;positivity) Z (columnCenter D B v) F (A*Z^(F+ε)) z (-leftHeight z)
      hZ (by positivity) (Or.inl rfl) (fun s=>(hmoment s ρ J₁ hJ₁ J₂ hJ₂ t ht).1)
    have hb₂ := hh₂ p hp hcop hg hpr pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
      (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
      (by intros;positivity) Z (columnCenter D B v) F (A*Z^(F+ε)) z (rightHeight z)
      hZ (by positivity) (Or.inr rfl) (fun s=>(hmoment s ρ J₁ hJ₁ J₂ hJ₂ t ht).2)
    rw [leftHeight_eq] at hb₁
    rw [rightHeight_eq] at hb₂
    have hh : 0≤tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2 := by
      dsimp [tripleHeight,coordinateHeight];positivity
    constructor
    · apply hb₁.trans
      gcongr
      linarith
    · apply hb₂.trans
      gcongr
      linarith
  have hb := hphysical p hp hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha
    ω₁ ω₂ Z D B v θ H R m η hZ.le hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F ((C₁+C₂)*(A*Z^(F+ε))) (by positivity) hm
  apply hb.trans
  have he : prefactorCenter m D B θ+3*η+F+R+π+(F+ε)≤m+11*η+π+ε := by
    rw [hF,hReq]
    exact InverseInitialEnergyCallerClipping.initial_scalar_le m D B v θ η _ π ε hδ
  have hexp := Real.rpow_add hZp (prefactorCenter m D B θ+3*η+F+R+π) (F+ε)
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le he
  calc
    _=(Cp*(C₁+C₂))*Z^(prefactorCenter m D B θ+3*η+F+R+π+(F+ε))*A*
        ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)) := by rw [hexp];ring
    _≤_ := by gcongr

end SevenEighths.InverseInitialEnergyCallerReference

end

end OAI

end Source2428

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstProfileIdentity.lean; sha256: 349a6c19fae2e65ef8627aef3637edbf7bc47d2365097016baaa490aa39e99e3 -/
section Source2429
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def firstNormProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 9 → ℝ → ℂ) (R : ℝ) (q : Fin 9 → ℝ) : ℂ :=
  (∏ i, V i (Real.log (q i))) * W₁ (q 0*q 2*q 5*q 7) *
    W₂ (q 1*q 2*q 5*q 8) *
    paperRadialFourier Φ (R*q 6/(q 3*q 4*(q 5)^2*q 7*q 8)) /
      ((q 3:ℂ)*(Real.sqrt (q 4):ℂ)*(q 5:ℂ)*
        (Real.sqrt (q 7):ℂ)*(Real.sqrt (q 8):ℂ))

theorem firstPoissonProfile_log (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 9 → ℝ → ℂ) (R : ℝ) (q : Fin 9 → ℝ) (hq : ∀ i, 0 < q i) :
    firstPoissonProfile W₁ W₂ Φ V R (fun i => Real.log (q i)) =
      firstNormProfile W₁ W₂ Φ V R q := by
  have hl : (∑ i, firstLeftSlope i * Real.log (q i)) =
      Real.log (q 0)+Real.log (q 2)+Real.log (q 5)+Real.log (q 7) := by
    simp [Fin.sum_univ_succ,firstLeftSlope]; ring
  have hr : (∑ i, firstRightSlope i * Real.log (q i)) =
      Real.log (q 1)+Real.log (q 2)+Real.log (q 5)+Real.log (q 8) := by
    simp [Fin.sum_univ_succ,firstRightSlope]; ring
  have hk : (∑ i, firstKernelSlope i * Real.log (q i)) =
      Real.log (q 6) - (Real.log (q 3)+Real.log (q 4)+Real.log (q 5)+
        Real.log (q 5)+Real.log (q 7)+Real.log (q 8)) := by
    simp [Fin.sum_univ_succ,firstKernelSlope]; ring
  unfold firstPoissonProfile firstNormProfile
  rw [hl,hr,hk]
  simp only [Real.exp_add,Real.exp_sub,Real.exp_log (hq _)]
  rw [show R*(q 6/(q 3*q 4*q 5*q 5*q 7*q 8)) =
    R*q 6/(q 3*q 4*(q 5)^2*q 7*q 8) from by ring]
  simp only [Fin.prod_univ_succ,firstRootWindows,inverseNormWindow,inverseRootWindow,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.isValue,Real.exp_log (hq _),
    Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,Fin.val_mk]
  norm_num
  ring

theorem canonicalPairMode_whole_profile {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C K : ℝ) (d h : Eis) :
    (‖eisEmbedding d‖^2 : ℂ)⁻¹ *
      canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ Φ
        (fun y => W₁ (A₁*C*Real.exp y)) (fun y => W₂ (A₂*C*Real.exp y)) 1 1 K d h =
    (K:ℂ) * firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
      ![A₁,A₂,C,‖eisEmbedding d‖^2,primeProductNorm p (cubeActiveSupport B v ε₁ ε₂),
        1,‖eisEmbedding h‖^2,primeProductNorm p N,primeProductNorm p P] *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  have hNC : Disjoint N (cubeActiveSupport B v ε₁ ε₂) :=
    hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P (cubeActiveSupport B v ε₁ ε₂) :=
    hPB.mono_right (Finset.filter_subset _ _)
  have hs (S : Finset ι) : ‖eisEmbedding (∏ i ∈ S,p i)‖ =
      Real.sqrt (primeProductNorm p S) := by
    simp only [primeProductNorm,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  unfold canonicalPairMode firstNormProfile
  simp only [columnLog,div_one,Real.exp_log (primeProductNorm_pos p hp _),
    Matrix.cons_val_zero,Fin.isValue,
    Finset.prod_const_one,one_mul,]
  rw [primeProductNorm_union p (N ∪ P) _ (Finset.disjoint_union_left.mpr ⟨hNC,hPC⟩),
    primeProductNorm_union p N P hNP]
  rw [Finset.prod_union (Finset.disjoint_union_left.mpr ⟨hNC,hPC⟩),Finset.prod_union hNP]
  simp only [map_mul,norm_mul,hs]
  rw [show K*‖eisEmbedding h‖^2 /
      (‖eisEmbedding d‖^2*(primeProductNorm p N*primeProductNorm p P*
        primeProductNorm p (cubeActiveSupport B v ε₁ ε₂))) =
      K*‖eisEmbedding h‖^2 /
      (‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*
        primeProductNorm p N*primeProductNorm p P) from by ring]
  push_cast
  ring_nf

end
end SevenEighths.InverseMoment

end OAI

end Source2429

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstNominal.lean; sha256: 03a4dc3d1398b0ad0829cffc0ea5ad1234d9187d06e1017528995efe52bdd654 -/
section Source2430
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
noncomputable section

def firstRootScale (s : Fin 9 → ℝ) : ℝ :=
  s 3 * Real.sqrt (s 4) * s 5 * Real.sqrt (s 7) * Real.sqrt (s 8)

theorem firstRootScale_pos (s : Fin 9 → ℝ) (hs : ∀ i, 0 < s i) :
    0 < firstRootScale s := by
  unfold firstRootScale
  exact mul_pos (mul_pos (mul_pos (mul_pos (hs 3) (Real.sqrt_pos.2 (hs 4)))
    (hs 5)) (Real.sqrt_pos.2 (hs 7))) (Real.sqrt_pos.2 (hs 8))

theorem firstNormProfile_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 9 → ℝ → ℂ) (s q : Fin 9 → ℝ)
    (hs : ∀ i, 0 < s i) (hq : ∀ i, 0 < q i) (K : ℝ) :
    firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
      (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ
      (fun i y => V i (y-Real.log (s i))) K q =
    ((firstRootScale s : ℝ):ℂ)⁻¹ *
      firstNormProfile W₁ W₂ Φ V (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))
        (fun i => q i/s i) := by
  have hl : (q 0/s 0)*(q 2/s 2)*(q 5/s 5)*(q 7/s 7) =
      q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7) := by ring
  have hr : (q 1/s 1)*(q 2/s 2)*(q 5/s 5)*(q 8/s 8) =
      q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8) := by ring
  have hk : (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))*(q 6/s 6)/
      ((q 3/s 3)*(q 4/s 4)*(q 5/s 5)^2*(q 7/s 7)*(q 8/s 8)) =
      K*q 6/(q 3*q 4*(q 5)^2*q 7*q 8) := by
    field_simp [(hs 3).ne', (hs 4).ne', (hs 5).ne', (hs 6).ne', (hs 7).ne', (hs 8).ne']
  have hd : (q 3/s 3)*Real.sqrt (q 4/s 4)*(q 5/s 5)*
      Real.sqrt (q 7/s 7)*Real.sqrt (q 8/s 8) =
      (q 3*Real.sqrt (q 4)*q 5*Real.sqrt (q 7)*Real.sqrt (q 8))/firstRootScale s := by
    rw [Real.sqrt_div (hq 4).le,Real.sqrt_div (hq 7).le,Real.sqrt_div (hq 8).le]
    unfold firstRootScale
    ring
  unfold firstNormProfile
  simp only [Real.log_div (hq _).ne' (hs _).ne']
  rw [hl,hr,hk]
  have hdC : (↑(q 3/s 3):ℂ)*↑(Real.sqrt (q 4/s 4))*↑(q 5/s 5)*
      ↑(Real.sqrt (q 7/s 7))*↑(Real.sqrt (q 8/s 8)) =
      ((q 3:ℂ)*↑(Real.sqrt (q 4))*(q 5:ℂ)*↑(Real.sqrt (q 7))*↑(Real.sqrt (q 8)))/
        (firstRootScale s:ℂ) := by exact_mod_cast hd
  rw [hdC]
  have hDc : (firstRootScale s:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (firstRootScale_pos s hs).ne'
  field_simp [hDc]

end
end SevenEighths.InverseMoment

end OAI

end Source2430

/- Original source: OAI/NumberTheory/DirichletL/Descent/PhysicalExponents.lean; sha256: e42b4d828ae468c90f999fe013861a11965ec5aa3e0426864cac862f5e1d907c -/
section Source2431
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section

theorem firstRootScale_rpow (Z : ℝ) (hZ : 0 < Z) (s : Fin 9 → ℝ) :
    firstRootScale (fun i => Z^(s i)) = Z^(s 3+s 4/2+s 5+s 7/2+s 8/2) := by
  have hs (x : ℝ) : Real.sqrt (Z^x) = Z^(x/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hZ.le]
    congr 1
    ring
  unfold firstRootScale
  rw [hs,hs,hs,← Real.rpow_add hZ,← Real.rpow_add hZ,← Real.rpow_add hZ,← Real.rpow_add hZ]

def firstKappa (M r ell V δ A B R : ℝ) : ℝ := M-2*r-2*ell-V-δ+A+B-R/2
def firstPhysicalHeight (M r ell V δ B j : ℝ) : ℝ := 2*r-2*B-M+4*ell+2*V+δ-j
def secondLambda (M r ell V δ A B j t g θ : ℝ) : ℝ :=
  firstPhysicalHeight M r ell V δ B j - θ - (r-A-B-t-g)
def secondCount (ell R j t g θ : ℝ) : ℝ := ell+R/2-j+t+g-θ
def secondFormalColumn (r A B t g v : ℝ) : ℝ := r-A-B-t-g-v
def secondFormalLabel (B θ v j : ℝ) : ℝ := B+θ+v+j

theorem first_physical_scalar (Z : ℝ) (hZ : 0 < Z)
    (M r ell V δ A₁ A₂ B R t h : ℝ) :
    Z^(-r-2*ell-V) * Z^M /
      firstRootScale (fun i => Z^(![A₁,A₂,B,δ,R,t,h,r-A₁-B-t,r-A₂-B-t] i)) =
    Z^((firstKappa M r ell V δ A₁ B R+firstKappa M r ell V δ A₂ B R)/2) := by
  rw [firstRootScale_rpow Z hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
  congr 1
  norm_num [firstKappa]
  ring

theorem second_physical_scalar (Z : ℝ) (hZ : 0 < Z)
    (M r ell V δ A B j t g θ v η τ : ℝ) :
    Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ) /
      (Z^θ*Z^v*Z^(secondFormalColumn r A B t g v)) * Real.exp (6*(η*Real.log Z)) =
    Z^(secondLambda M r ell V δ A B j t g θ+18*η+τ) := by
  have he : Real.exp (6*(η*Real.log Z)) = Z^(6*η) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  rw [he,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ,←Real.rpow_add hZ]
  congr 1
  unfold secondLambda secondFormalColumn
  ring

theorem physical_prefactor_identity (M r ell V δ A B R j t g θ v : ℝ) :
    firstKappa M r ell V δ A B R + secondLambda M r ell V δ A B j t g θ +
      secondCount ell R j t g θ +
      2*(secondFormalColumn r A B t g v+secondFormalLabel B θ v j) = r+3*ell+V := by
  unfold firstKappa secondLambda firstPhysicalHeight secondCount secondFormalColumn secondFormalLabel
  ring

theorem physical_step_energy_exponent (M r ell V δ A B R j t g θ v η τ π ε clip : ℝ)
    (hclip : clip ≤ 6*η) :
    firstKappa M r ell V δ A B R + secondLambda M r ell V δ A B j t g θ +
      secondCount ell R j t g θ +
      2*(secondFormalColumn r A B t g v+secondFormalLabel B θ v j+clip) +
      (9/2+18+11/2)*η+τ+π+ε ≤ r+3*ell+V+40*η+τ+π+ε :=
  step_energy_exponent (physical_prefactor_identity M r ell V δ A B R j t g θ v) hclip

end
end SevenEighths.InverseMoment

end OAI

end Source2431

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstRowGeometry.lean; sha256: bb3dc58b157290278ca53f3b39e919c1fc82e0c99a3bb9e54b99567ea788571b -/
section Source2432
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma first_whole_frequency_numeric (K P dn an cn a1 a2 sn tn hn L : ℝ)
    (hK : 0<K) (hP : 0<P) (hdn : 0<dn) (han : 0<an)
    (hcn : 0<cn) (ha1 : 0<a1) (ha2 : 0<a2)
    (hsn : 0<sn) (htn : 0<tn) (_hhn : 0≤hn) (hL : 0<L)
    (hS : a1*cn*sn≤L) (hT : a2*cn*tn≤L)
    (hratio : (K/(dn*(sn*tn*an)))*hn≤P) :
    hn≤L^2*an*dn/((K/P)*a1*a2*cn^2) := by
  have hprod : sn*tn*(a1*a2*cn^2)≤L^2 := by
    have hh := mul_le_mul hS hT (by positivity : 0≤a2*cn*tn) hL.le
    nlinarith [hh]
  have hraw : K*hn≤P*(dn*(sn*tn*an)) := by
    rw [div_mul_eq_mul_div] at hratio
    exact (div_le_iff₀ (by positivity)).mp hratio
  have hfull : K*hn*(a1*a2*cn^2)≤P*dn*an*L^2 := by
    have hh := mul_le_mul_of_nonneg_right hraw (by positivity : 0≤a1*a2*cn^2)
    have hh' := mul_le_mul_of_nonneg_left hprod (by positivity : 0≤P*dn*an)
    nlinarith [hh,hh']
  apply (le_div_iff₀ (by positivity)).mpr
  convert div_le_div_of_nonneg_right hfull hP.le using 1 <;> field_simp

theorem first_ratio_actual_row {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (S N Q : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i)
    (hNQ : Disjoint N Q) (hNS : Disjoint N S) (hQS : Disjoint Q S)
    (common divisor : Finset ι) (f : Ideal O) (h : O)
    (K P L B F : ℝ) (hK : 0<K) (hP : 0<P) (hL : 0<L) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤B)
    (hf : (Ideal.absNorm f : ℝ)≤F)
    (hcol₁ : ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p N≤L)
    (hcol₂ : ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p Q≤L)
    (hratio : (K/(primeProductNorm p divisor *
      primeProductNorm p ((N∪Q)∪cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂)))*‖eisEmbedding h‖^2≤P) :
    ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂) (f,h))‖^2 ≤
    P*L^2*B^4*F^2*primeProductNorm p divisor /
      (K*(primeProductNorm p common)^2*‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2) := by
  let active := cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂
  let e := dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂
  let j := jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂
  let a1 := aLabel p S ε₁
  let a2 := aLabel p S ε₂
  have hactive : active ⊆ S := Finset.filter_subset _ _
  have hnorm : primeProductNorm p ((N∪Q)∪active)=
      primeProductNorm p N*primeProductNorm p Q*primeProductNorm p active := by
    rw [primeProductNorm_union p (N∪Q) active (Finset.disjoint_union_left.mpr
      ⟨hNS.mono_right hactive,hQS.mono_right hactive⟩),
      primeProductNorm_union p _ _ hNQ]
  change (K/(primeProductNorm p divisor*primeProductNorm p ((N∪Q)∪active)))*‖eisEmbedding h‖^2≤P at hratio
  rw [hnorm] at hratio
  have hpos (v : ι→ℕ) : 0<‖eisEmbedding (primeProduct p S v)‖^2 :=
    SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
  have hfreq := first_whole_frequency_numeric K P (primeProductNorm p divisor)
    (primeProductNorm p active) (primeProductNorm p common) (‖eisEmbedding a1‖^2)
    (‖eisEmbedding a2‖^2) (primeProductNorm p N) (primeProductNorm p Q)
    (‖eisEmbedding h‖^2) L hK hP (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _)
    (primeProductNorm_pos p hp _) (hpos _) (hpos _) (primeProductNorm_pos p hp _)
    (primeProductNorm_pos p hp _) (sq_nonneg _) hL hcol₁ hcol₂ hratio
  have hcon := first_conductor_norm_bound p hp S v₁ v₂ ε₁ ε₂ hv B hB.le hb₁ hb₂
  have hnum := first_row_numeric_bound (primeProductNorm p active) (‖eisEmbedding e‖^2)
    (‖eisEmbedding j‖^2) (‖eisEmbedding a1‖^2) (‖eisEmbedding a2‖^2)
    (primeProductNorm p common) (primeProductNorm p divisor) (‖eisEmbedding h‖^2)
    (Ideal.absNorm f) L (K/P) B F (primeProductNorm_pos p hp _).le (sq_nonneg _)
    (hpos _) (hpos _) (hpos _) (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _).le
    (sq_nonneg _) (Nat.cast_nonneg _) hL (div_pos hK hP) hB hF hcon hfreq hf
  have hgen : ‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator f)‖^2=(Ideal.absNorm f : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ConcretePrimeRowBridge.span_idealGenerator]
  have hrow : ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap e (f,h))‖^2 =
      ‖eisEmbedding h‖^2*(Ideal.absNorm f : ℝ)^2*‖eisEmbedding e‖^2 := by
    simp only [DescentWeightedCauchy.firstElementRowMap,map_mul,map_pow,norm_mul,norm_pow,mul_pow]
    rw [hgen]
  rw [hrow]
  apply hnum.trans_eq
  field_simp
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2432

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstCutoffScale.lean; sha256: 1c67095d68b638129bc5ec05b143045c897ede8db54c2d83042fd308f412b9f5 -/
section Source2433
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem first_physical_row_scale_bound
    (Z M r ell V delta B j eta tau dn cn jn : ℝ) (hZ : 0<Z)
    (_hdn : 0≤dn) (hcn : 0<cn) (_hjn : 0<jn)
    (hd : dn≤Z^(delta+eta)) (hc : Z^(B-eta)≤cn) (hj : Z^(j-eta)≤jn) :
    Z^tau*(Z^(r+eta))^2*(Z^(ell+eta))^4*(Z^(V+eta))^2*dn /
      (Z^M*cn^2*jn) ≤ Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau) := by
  have hpow (x : ℝ) (n : ℕ) : (Z^x)^n=Z^(x*n) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  calc
    _ ≤ Z^tau*(Z^(r+eta))^2*(Z^(ell+eta))^4*(Z^(V+eta))^2*Z^(delta+eta) /
        (Z^M*(Z^(B-eta))^2*Z^(j-eta)) := by
      apply div_le_div₀ (by positivity)
      · exact mul_le_mul_of_nonneg_left hd (by positivity)
      · positivity
      · exact mul_le_mul (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.rpow_pos_of_pos hZ _).le hc 2) (Real.rpow_pos_of_pos hZ _).le)
          hj (Real.rpow_pos_of_pos hZ _).le (by positivity)
    _ = _ := by
      simp only [hpow,←Real.rpow_add hZ,←Real.rpow_sub hZ]
      congr 1
      unfold firstPhysicalHeight
      norm_num
      ring

theorem first_ratio_canonical_row {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (S N Q : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i)
    (hNQ : Disjoint N Q) (hNS : Disjoint N S) (hQS : Disjoint Q S)
    (common divisor : Finset ι) (f : Ideal O) (h : O)
    (Z M r ell V delta B j eta tau : ℝ) (hZ : 0<Z)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤Z^(ell+eta))
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤Z^(ell+eta))
    (hf : (Ideal.absNorm f : ℝ)≤Z^(V+eta))
    (hd : primeProductNorm p divisor≤Z^(delta+eta))
    (hc : Z^(B-eta)≤primeProductNorm p common)
    (hj : Z^(j-eta)≤‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2)
    (hcol₁ : ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p N≤Z^(r+eta))
    (hcol₂ : ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p Q≤Z^(r+eta))
    (hratio : (Z^M/(primeProductNorm p divisor *
      primeProductNorm p ((N∪Q)∪cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂)))*‖eisEmbedding h‖^2≤Z^tau) :
    ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂) (f,h))‖^2 ≤
      Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau) := by
  have hrow := first_ratio_actual_row p hp S N Q v₁ v₂ ε₁ ε₂ hv hNQ hNS hQS common divisor f h
    (Z^M) (Z^tau) (Z^(r+eta)) (Z^(ell+eta)) (Z^(V+eta))
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hb₁ hb₂ hf hcol₁ hcol₂ hratio
  exact hrow.trans (first_physical_row_scale_bound Z M r ell V delta B j eta tau
    (primeProductNorm p divisor) (primeProductNorm p common)
    (‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2) hZ
    (primeProductNorm_pos p hp _).le (primeProductNorm_pos p hp _)
    (SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)) hd hc hj)

end
end SevenEighths.InverseMoment

end OAI

end Source2433

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstPhysicalCutoff.lean; sha256: eddeeee94eedba9116d5411a4200e1b6ea4ed6201bf735fac78dcbd8b69e99f0 -/
section Source2434
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def firstPhysicalMultiplier {ι : Type*} (p : ι→O) (S : Finset ι)
    (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool) (f : Ideal O) : O :=
  (ConcretePrimeRowBridge.idealGenerator f)^2 * dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂

lemma firstPhysicalMultiplier_ne_zero {ι : Type*} (p : ι→O) (hp : ∀ i,p i≠0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (S : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool) (f : Ideal O) (hf : f≠0) :
    firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f≠0 :=
  mul_ne_zero (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero f hf))
    (primeProduct_ne_zero p hp _ _)

lemma firstPhysicalMultiplier_row {ι : Type*} (p : ι→O) (S : Finset ι)
    (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool) (f : Ideal O) (h : O) :
    firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f*h =
      DescentWeightedCauchy.firstElementRowMap (dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂) (f,h) := by
  unfold firstPhysicalMultiplier DescentWeightedCauchy.firstElementRowMap
  ring

theorem first_physical_cutoff_raw_tail {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (S N Q : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i)
    (hNQ : Disjoint N Q) (hNS : Disjoint N S) (hQS : Disjoint Q S)
    (common divisor : Finset ι) (f : Ideal O) (hf0 : f≠0) (h : O)
    (Z M r ell V delta B j eta tau : ℝ) (hZ : 0<Z)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤Z^(ell+eta))
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤Z^(ell+eta))
    (hf : (Ideal.absNorm f : ℝ)≤Z^(V+eta))
    (hd : primeProductNorm p divisor≤Z^(delta+eta))
    (hc : Z^(B-eta)≤primeProductNorm p common)
    (hj : Z^(j-eta)≤‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2)
    (hcol₁ : ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p N≤Z^(r+eta))
    (hcol₂ : ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p Q≤Z^(r+eta))
    (hout : h∉childFrequencyBall (firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f)
      (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))) :
    Z^tau ≤ (Z^M/(primeProductNorm p divisor *
      primeProductNorm p ((N∪Q)∪cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂)))*‖eisEmbedding h‖^2 := by
  by_contra hbad
  have hratio := (lt_of_not_ge hbad).le
  have hrow := first_ratio_canonical_row p hp S N Q v₁ v₂ ε₁ ε₂ hv hNQ hNS hQS common divisor f h
    Z M r ell V delta B j eta tau hZ hb₁ hb₂ hf hd hc hj hcol₁ hcol₂ hratio
  apply hout
  apply (mem_childFrequencyBall _ (firstPhysicalMultiplier_ne_zero p hp S v₁ v₂ ε₁ ε₂ f hf0) _ h).mpr
  simpa only [firstPhysicalMultiplier_row] using hrow

end
end SevenEighths.InverseMoment

end OAI

end Source2434

/- Original source: OAI/NumberTheory/DirichletL/Descent/MarkedTails.lean; sha256: fda07f95ad44cacd7af7f91bceb2938b3ca7e1c666ee910da5f7312b6a1681c2 -/
section Source2435
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def markedColumn {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (C : Finset ι → ℂ) (U : Finset ι) : ℂ :=
  primeMark slots lists a (A ∪ U) * C U

lemma markedColumn_source_support {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (C : Finset ι → ℂ) (U : Finset ι)
    (h : markedColumn slots lists a A C U ≠ 0) : C U ≠ 0 :=
  (mul_ne_zero_iff.mp h).2

theorem markedColumn_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (C : Finset ι → ℂ) (G X M : ℝ),
      0 ≤ G → 0 < X →
      (∀ U ∈ F.powerset, ‖C U‖ ≤ G) →
      (∀ U ∈ F.powerset, C U ≠ 0 → columnLog p X U ≤ M) →
      ∀ U ∈ F.powerset, ‖markedColumn slots lists a A C U‖ ≤
        (2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * G := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_extracted_bound ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A F C G X M hG hX hC hsupport U hU
  by_cases hz : C U = 0
  · simp only [markedColumn,hz,mul_zero,norm_zero]
    positivity
  · have hn := columnLog_norm_upper p hp X M hX U (hsupport U hU hz)
    rw [markedColumn,norm_mul]
    have hm := hmark p hp hcop slots lists a hslots ha A U
    have hnorm : 0 < primeProductNorm p U := primeProductNorm_pos p hp U
    apply (mul_le_mul hm (hC U hU) (norm_nonneg _) (by positivity)).trans
    gcongr

theorem marked_first_kernel_remainder (ε : ℝ) (hε : 0 < ε) (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct Cm : ℝ), 0 < Ct ∧ 0 < Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
      (F B A₁ A₂ : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool), Disjoint F B →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
        (a₁ a₂ : σ → ι → ℂ),
      (slots₁ : Set σ).PairwiseDisjoint lists₁ → (slots₂ : Set σ).PairwiseDisjoint lists₂ →
      (∀ i ∈ slots₁, ∀ k ∈ lists₁ i, ‖a₁ i k‖ ≤ 1) →
      (∀ i ∈ slots₂, ∀ k ∈ lists₂ i, ‖a₂ i k‖ ≤ 1) →
      ∀ (C₁ C₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0 ≤ G₁ → 0 ≤ G₂ → 0 < X₁ → 0 < X₂ → 0 < K → 0 ≤ P →
      (∀ U ∈ F.powerset, ‖C₁ U‖ ≤ G₁) → (∀ U ∈ F.powerset, ‖C₂ U‖ ≤ G₂) →
      (∀ U ∈ F.powerset, C₁ U ≠ 0 → columnLog p X₁ U ≤ M₁) →
      (∀ U ∈ F.powerset, C₂ U ≠ 0 → columnLog p X₂ U ≤ M₂) →
      ∀ d : Eis, d ≠ 0 →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let G₁' := (2:ℝ)^A₁.card * Cm * U₁^ε * G₁
      let G₂' := (2:ℝ)^A₂.card * Cm * U₂^ε * G₂
      let slow := K/(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑' h : {h : Eis // h ∉ T}, actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (markedColumn slots₁ lists₁ a₁ A₁ C₁) (markedColumn slots₂ lists₂ a₂ A₂ C₂)
        W (fun _ => 1) (fun _ => 1) X₁ X₂ K d h.val‖ ≤
      (128*U₁)*(128*U₂)*(G₁'*G₂'*K) *
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_uniform_actualFirstKernel_disk_remainder order
  obtain ⟨Cm,hCm,hmark⟩ := markedColumn_uniform_bound ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc F B A₁ A₂ v ε₁ ε₂ hFB
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ hl₁ hl₂ ha₁ ha₂ C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂
    hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hs₁ hs₂ d hd
  apply htail p hp hinj hcop hg hc F B v ε₁ ε₂ hFB _ _ W _ _ X₁ X₂ K P M₁ M₂
    (by positivity) (by positivity) hX₁ hX₂ hK hP
  · exact hmark p hp hcop slots₁ lists₁ a₁ hl₁ ha₁ A₁ F C₁ G₁ X₁ M₁ hG₁ hX₁ hC₁ hs₁
  · exact hmark p hp hcop slots₂ lists₂ a₂ hl₂ ha₂ A₂ F C₂ G₂ X₂ M₂ hG₂ hX₂ hC₂ hs₂
  · intro U hU hn
    exact hs₁ U hU (markedColumn_source_support _ _ _ _ _ _ hn)
  · intro U hU hn
    exact hs₂ U hU (markedColumn_source_support _ _ _ _ _ _ hn)
  · exact hd

end
end SevenEighths.InverseMoment

end OAI

end Source2435

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstWholeTail.lean; sha256: cd1ee6c99d1959fb7d2e8b1a70f9bdd4b6d595e48a6af4cbc6f985f976eb0a66 -/
section Source2436
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_first_supported_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),Disjoint F B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0≤G₁ → 0≤G₂ → 0<X₁ → 0<X₂ → 0<K → 0≤P →
      (∀N∈F.powerset,‖C₁ N‖≤G₁) → (∀N∈F.powerset,‖C₂ N‖≤G₂) →
      (∀N∈F.powerset,C₁ N≠0 → columnLog p X₁ N≤M₁) →
      (∀N∈F.powerset,C₂ N≠0 → columnLog p X₂ N≤M₂) →
      ∀(d : O),d≠0 → ∀ T : Finset O,
      (∀ N∈F.powerset,∀ Q∈F.powerset,Disjoint N Q → C₁ N≠0 → C₂ Q≠0 →
        ∀ h : O,h∉T → P≤(K/(‖eisEmbedding d‖^2*
          primeProductNorm p ((N∪Q)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2) →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let slow := K/(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*K)*
        ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+P)^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc F B v ε₁ ε₂ hFB C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂ hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hS₁ hS₂ d hd T hT
  dsimp only
  let U₁:=X₁*Real.exp M₁
  let U₂:=X₂*Real.exp M₂
  let S:=cubeActiveSupport B v ε₁ ε₂
  let slow:=K/(‖eisEmbedding d‖^2*primeProductNorm p S*U₁*U₂)
  let tail:ℝ:=(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 slow)^2*(1+P)^A)
  let Q:ℝ:=G₁*G₂*K*tail
  have hU₁:0<U₁:=mul_pos hX₁ (Real.exp_pos _)
  have hU₂:0<U₂:=mul_pos hX₂ (Real.exp_pos _)
  have hNd:0<‖eisEmbedding d‖^2:=sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hslow:0<slow:=div_pos hK (mul_pos (mul_pos (mul_pos hNd (primeProductNorm_pos p hp S)) hU₁) hU₂)
  have hH:0≤P:=hP
  have htail:0≤tail:=by dsimp [tail]; positivity
  have hQ:0≤Q:=mul_nonneg (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le) htail
  let rem (N R:Finset ι):ℂ:=if Disjoint N R then
    ∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val else 0
  have hnzero (N R:Finset ι) (hn:C₁ N=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hn]
  have hrzero (N R:Finset ι) (hr:C₂ R=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hr]
  have heq : (∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val)=
      ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,rem N R := by
    rw [actualFirstKernel_complement_eq_pairs p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K hK d hd T]
    change (∑N∈F.powerset,∑R∈F.powerset,rem N R)=_
    calc
      _ = ∑N∈boundedPrimeSupports p F U₁,∑R∈F.powerset,rem N R := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro N hN hn
        have hz:C₁ N=0:=by
          by_contra h
          exact hn (Finset.mem_filter.mpr ⟨hN,columnLog_norm_upper p hp X₁ M₁ hX₁ N (hS₁ N hN h)⟩)
        simp only [hnzero N _ hz,Finset.sum_const_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro N hN
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro R hR hr
        have hz:C₂ R=0:=by
          by_contra h
          exact hr (Finset.mem_filter.mpr ⟨hR,columnLog_norm_upper p hp X₂ M₂ hX₂ R (hS₂ R hR h)⟩)
        exact hrzero N R hz
  have hrem (N:Finset ι) (hN:N∈boundedPrimeSupports p F U₁) (R:Finset ι) (hR:R∈boundedPrimeSupports p F U₂):‖rem N R‖≤Q:=by
    have hNF: N∈F.powerset:=(Finset.mem_filter.mp hN).1
    have hRF: R∈F.powerset:=(Finset.mem_filter.mp hR).1
    by_cases hn:C₁ N=0
    · rw [hnzero N R hn,norm_zero]; exact hQ
    by_cases hr:C₂ R=0
    · rw [hrzero N R hr,norm_zero]; exact hQ
    by_cases hNR:Disjoint N R
    · have hNB:=hFB.mono_left (Finset.mem_powerset.mp hNF)
      have hRB:=hFB.mono_left (Finset.mem_powerset.mp hRF)
      have hNS:Disjoint N S:=hNB.mono_right (Finset.filter_subset _ _)
      have hRS:Disjoint R S:=hRB.mono_right (Finset.filter_subset _ _)
      have hnorm:primeProductNorm p ((N∪R)∪S)=primeProductNorm p N*primeProductNorm p R*primeProductNorm p S:=by
        rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hNS,hRS⟩),primeProductNorm_union p _ _ hNR]
      have hprod:=mul_le_mul (Finset.mem_filter.mp hN).2 (Finset.mem_filter.mp hR).2
        (primeProductNorm_pos p hp R).le hU₁.le
      have hscale:slow≤K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S)):=by
        apply div_le_div_of_nonneg_left hK.le (mul_pos hNd (primeProductNorm_pos p hp _))
        rw [hnorm]
        calc
          _ ≤ ‖eisEmbedding d‖^2*(U₁*U₂*primeProductNorm p S):=mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
          _ = _ := by ring
      have hnroot:1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖:=by
        have hx:=primeProductNorm_ge_one p hp ((N∪R)∪S)
        change 1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖^2 at hx
        nlinarith [norm_nonneg (eisEmbedding (∏i∈(N∪R)∪S,p i))]
      have hpre:(K/‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖)*(‖C₁ N‖*‖C₂ R‖)≤G₁*G₂*K:=by
        calc
          _ ≤ K*(G₁*G₂):=mul_le_mul (div_le_self hK.le hnroot)
            (mul_le_mul (hC₁ N hNF) (hC₂ R hRF) (norm_nonneg _) hG₁)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK.le
          _ = _ := by ring
      have hfrac:(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S))))^2*(1+P)^A)≤tail:=by
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos (sq_pos_of_pos (lt_min (by norm_num) hslow)) (pow_pos (by linarith) _))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_min zero_le_one hslow.le)
          (min_le_min_left 1 hscale) 2) (pow_nonneg (by linarith) _)
      have hpair:=hb p hp hcop hg hc N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1)
        X₁ X₂ K P hK hP d hd T (hT N hNF R hRF hNR hn hr)
      simp only [norm_one,one_mul] at hpair
      dsimp only [rem]
      rw [ite_eq_left hNR]
      exact hpair.trans (mul_le_mul hpre hfrac (by positivity) (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le))
    · simp only [rem,ite_eq_right hNR,norm_zero];exact hQ
  rw [heq]
  calc
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,‖rem N R‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun N hN=>norm_sum_le _ _))
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,Q:=
      Finset.sum_le_sum (fun N hN=>Finset.sum_le_sum (fun R hR=>hrem N hN R hR))
    _ = ((boundedPrimeSupports p F U₁).card:ℝ)*((boundedPrimeSupports p F U₂).card:ℝ)*Q:=by simp;ring
    _ ≤ (128*U₁)*(128*U₂)*Q:=mul_le_mul_of_nonneg_right
      (mul_le_mul (boundedPrimeSupports_card_positive p hp hinj F U₁ hU₁)
        (boundedPrimeSupports_card_positive p hp hinj F U₂ hU₂) (Nat.cast_nonneg _) (by positivity)) hQ
    _ = _ := by dsimp [Q,tail,slow,U₁,U₂,S];ring

end
end SevenEighths.InverseMoment

end OAI

end Source2436

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstPhysicalTail.lean; sha256: 432dda7c3ea59986502eb3701eb085329940fea2ee5ef1c4d7a59fe98b27a9ae -/
section Source2437
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_first_physical_tail (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool S common divisor : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      (∀ i∈S,0<v₁ i+v₂ i) → Disjoint pool S →
      ∀ (f : Ideal O),f≠0 → ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (G₁ G₂ Z M r ell V delta B j eta tau : ℝ),0≤G₁ → 0≤G₂ → 0<Z →
      (∀ U∈pool.powerset,‖C₁ U‖≤G₁) → (∀ U∈pool.powerset,‖C₂ U‖≤G₂) →
      ‖eisEmbedding (primeProduct p S v₁)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p S v₂)‖^2≤Z^(ell+eta) →
      (Ideal.absNorm f : ℝ)≤Z^(V+eta) → primeProductNorm p divisor≤Z^(delta+eta) →
      Z^(B-eta)≤primeProductNorm p common →
      Z^(j-eta)≤‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2 →
      (∀ N∈pool.powerset,C₁ N≠0 →
        ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p N≤Z^(r+eta)) →
      (∀ Q∈pool.powerset,C₂ Q≠0 →
        ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p Q≤Z^(r+eta)) →
      let U₁ := Z^(r+eta)/(‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common)
      let U₂ := Z^(r+eta)/(‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common)
      let active := cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂
      let slow := Z^M/(primeProductNorm p divisor*primeProductNorm p active*U₁*U₂)
      let T := childFrequencyBall (firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f)
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
      ‖∑' h : {h : O // h∉T},actualFirstKernel p hp hcop hg pool S (fun i=>v₁ i+v₂ i) ε₁ ε₂
        C₁ C₂ W (fun _=>1) (fun _=>1) 1 1 (Z^M)
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) divisor) h.val‖ ≤
      (128*U₁)*(128*U₂)*(G₁*G₂*Z^M)*
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 slow)^2*(1+Z^tau)^order)) := by
  obtain ⟨s,Ct,hCt,hfull⟩ := full_first_supported_remainder order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hinj hcop hg hchar pool S common divisor v₁ v₂ ε₁ ε₂ hv hpool f hf0
    C₁ C₂ W G₁ G₂ Z M r ell V delta B j eta tau hG₁ hG₂ hZ hC₁ hC₂ hb₁ hb₂ hf hd hc hj hcol₁ hcol₂
    U₁ U₂ active slow T
  have hA (ε : ι→Bool) : 0<‖eisEmbedding (aLabel p S ε)‖^2 :=
    SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
  have hU₁ : 0<U₁ := div_pos (Real.rpow_pos_of_pos hZ _)
    (mul_pos (hA ε₂) (primeProductNorm_pos p hp _))
  have hU₂ : 0<U₂ := div_pos (Real.rpow_pos_of_pos hZ _)
    (mul_pos (hA ε₁) (primeProductNorm_pos p hp _))
  have hlog₁ (N : Finset ι) (hN : N∈pool.powerset) (hn : C₁ N≠0) : columnLog p 1 N≤Real.log U₁ := by
    unfold columnLog
    rw [div_one]
    apply Real.log_le_log (primeProductNorm_pos p hp _)
    apply (le_div_iff₀ (mul_pos (hA ε₂) (primeProductNorm_pos p hp _))).mpr
    simpa only [mul_comm] using hcol₁ N hN hn
  have hlog₂ (N : Finset ι) (hN : N∈pool.powerset) (hn : C₂ N≠0) : columnLog p 1 N≤Real.log U₂ := by
    unfold columnLog
    rw [div_one]
    apply Real.log_le_log (primeProductNorm_pos p hp _)
    apply (le_div_iff₀ (mul_pos (hA ε₁) (primeProductNorm_pos p hp _))).mpr
    simpa only [mul_comm] using hcol₂ N hN hn
  have hb := hfull p hp hinj hcop hg hchar pool S (fun i=>v₁ i+v₂ i) ε₁ ε₂ hpool C₁ C₂ W
    G₁ G₂ 1 1 (Z^M) (Z^tau) (Real.log U₁) (Real.log U₂) hG₁ hG₂ zero_lt_one zero_lt_one
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _).le hC₁ hC₂ hlog₁ hlog₂
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) divisor) (primeSubsetGenerator_ne_zero _ _) T
    (fun N hN Q hQ hNQ hn hq h hout=>by
      simpa only [primeSubsetGenerator_norm_eq_productNorm, Finset.union_comm] using
        first_physical_cutoff_raw_tail p hp S Q N v₁ v₂ ε₁ ε₂ hv hNQ.symm
          (hpool.mono_left (Finset.mem_powerset.mp hQ)) (hpool.mono_left (Finset.mem_powerset.mp hN))
          common divisor f hf0 h Z M r ell V delta B j eta tau hZ hb₁ hb₂ hf hd hc hj
          (hcol₂ Q hQ hq) (hcol₁ N hN hn) hout)
  simpa only [Real.exp_log hU₁,Real.exp_log hU₂,one_mul,primeSubsetGenerator_norm_eq_productNorm]
    using hb

end
end SevenEighths.InverseMoment

end OAI

end Source2437

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstMarkedColumns.lean; sha256: a45f25331b7da7fba9e4018e776d68b0dfa30f8aec8f2df7a031dcaf947d08f2 -/
section Source2438
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]

theorem cube_whole_column_norm (p : ι→O) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C N : Finset ι) (hC : Disjoint C b.support) (hN : Disjoint N (b.support∪C))
    (negative : Bool) :
    primeProductNorm p (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N) =
      ‖eisEmbedding (aLabel p b.support (if negative then b.rightBit else b.leftBit))‖^2 *
        primeProductNorm p C * primeProductNorm p N := by
  have hd : (if negative then b.rightDivisor else b.leftDivisor) ⊆ b.support := by
    cases negative
    · exact hb.1
    · exact hb.2
  rw [primeProductNorm_union p _ _ (hN.symm.mono_left (Finset.union_subset_union hd (Finset.Subset.refl C))),
    primeProductNorm_union p _ _ (hC.symm.mono_left hd)]
  congr 2
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [CubeCoordinates.aLabel_left p b hb]; rfl
  · rw [CubeCoordinates.aLabel_right p b hb]; rfl

def wholeMarkedTest {σ : Type*} [DecidableEq σ] (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (test : Finset ι→ℂ) (U : Finset ι) : ℂ :=
  primeMark slots lists a U * test U

theorem whole_marked_test_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ, 0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test : Finset ι→ℂ) (G L : ℝ),0≤G → 0≤L →
      (∀ U,‖test U‖≤G) → (∀ U,test U≠0 → primeProductNorm p U≤L) →
      ∀ U,‖wholeMarkedTest slots lists a test U‖≤Cm*L^ε*G := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha test G L hG hL hb hs U
  by_cases hz : test U=0
  · simp only [wholeMarkedTest,hz,mul_zero,norm_zero]; positivity
  · have hn0 := (primeProductNorm_pos p hp U).le
    rw [wholeMarkedTest,norm_mul]
    calc
      _ ≤ (Cm*(primeProductNorm p U)^ε)*G :=
        mul_le_mul (hmark p hp hcop slots lists a hslots ha U) (hb U) (norm_nonneg _) (by positivity)
      _ ≤ Cm*L^ε*G := by gcongr; exact hs U hz

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_residual_norm (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (hΨ : ∀ u,‖Ψ u‖≤1) (m f : O) (H : Finset ι→ℂ) (N : Finset ι) :
    ‖canonicalCubeResidual p hg b C negative Ψ m f H N‖ ≤
      ‖H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N)‖ := by
  exact originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit negative
    Ψ hΨ m (∏i∈C,p i) f _ N

theorem canonical_residual_test_nonzero (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) (N : Finset ι)
    (hn : canonicalCubeResidual p hg b C negative Ψ m f H N≠0) :
    H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N)≠0 := by
  exact originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit negative
    Ψ m (∏i∈C,p i) f _ N hn

theorem canonical_marked_residual_support {σ : Type*} [DecidableEq σ]
    (b : CubeCoordinates ι) (hb : b.Admissible) (C N : Finset ι)
    (hC : Disjoint C b.support) (hN : Disjoint N (b.support∪C)) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (test : Finset ι→ℂ) (L : ℝ) (hs : ∀ U,test U≠0 → primeProductNorm p U≤L)
    (hn : canonicalCubeResidual p hg b C negative Ψ m f (wholeMarkedTest slots lists a test) N≠0) :
    ‖eisEmbedding (aLabel p b.support (if negative then b.rightBit else b.leftBit))‖^2 *
      primeProductNorm p C * primeProductNorm p N≤L := by
  have ht := canonical_residual_test_nonzero p hg b C negative Ψ m f _ N hn
  have htest := (mul_ne_zero_iff.mp ht).2
  simpa only [cube_whole_column_norm p b hb C N hC hN negative] using hs _ htest

end
end SevenEighths.InverseMoment

end OAI

end Source2438

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstModeColumns.lean; sha256: 6da8473ad8fbe65cf6d381ead2050144c1b6eca88b8a3c01b82d7fa75aa2aa35 -/
section Source2439
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FourierBridge JointLogSeparation
open MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def firstCoordinates (a : Fin 7 → ℝ) (x y : ℝ) : Fin 9 → ℝ :=
  ![a 0,a 1,a 2,a 3,a 4,a 5,a 6,x,y]

def firstOuterPhase (h : Fin 9 → ℝ) (a : Fin 7 → ℝ) : ℂ :=
  ∏ i : Fin 7, logPhase (h ⟨i.val, by omega⟩) (a i)

theorem first_mode_split (a : Fin 7 → ℝ) (x y : ℝ)
    (v : Frequency × (Fin 9 → ℝ)) :
    pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstCoordinates a x y) v.1 v.2 =
      firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2) a *
      logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2 7) x *
      logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2 8) y := by
  rw [pureProfileMode_height]
  simp [Fin.prod_univ_succ,firstCoordinates,firstOuterPhase]
  ring

def firstColumnMode (negative : Bool) {ι : Type*} (C : Finset ι → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * if negative then star (logPhase t (y S)) else logPhase t (y S)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem threeGaussRowFactor_first_mode (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (y₁ y₂ : Finset ι → ℝ) (t₁ t₂ : ℝ) (d h : Eis) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (firstColumnMode true C₁ y₁ t₁) (firstColumnMode false C₂ y₂ t₂) d h =
    logPhase t₁ (y₁ N) * logPhase t₂ (y₂ P) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  simp only [threeGaussRowFactor,firstColumnMode,Bool.false_eq_true,ite_false,ite_true,
    star_mul,star_star]
  ring

theorem actual_first_mode_ideal_rows
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (d h : Eis) (a : Fin 7 → ℝ) (y₁ y₂ : Finset ι → ℝ)
    (z : Frequency × (Fin 9 → ℝ)) :
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
          (firstCoordinates a (y₁ N) (y₂ P)) z.1 z.2 else 0) =
    firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2) a *
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂
          (firstColumnMode true C₁ y₁ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)) d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂
          (firstColumnMode false C₂ y₂ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)) d) h := by
  rw [mul_assoc, ← sum_threeGaussRowFactor_eq_ideal_rows p hp hinj hcop hg hc hpr F B hFB]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hd : Disjoint N P
  · simp only [hd,ite_true]
    rw [first_mode_split,threeGaussRowFactor_first_mode]
    ring
  · simp [hd]

end
end SevenEighths.InverseMoment

end OAI

end Source2439
